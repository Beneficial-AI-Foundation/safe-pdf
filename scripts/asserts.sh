#!/usr/bin/env bash
# Assertions build (task 13.10; Plan.md section 6 Phase 13, M13 part 3; section 4 S1, S3).
#
# Lake's release build passes `-O3 -DNDEBUG`, which compiles out the `assert(i < lean_array_size(o))`
# of lean.h's `lean_array_get_core` and its siblings: the check behind every proof-carrying index
# `a[i]'h`. This script builds `tests`, `fuzz`, `inspect` and `worker` (plus `worker-probe` and
# `assert-rig`) WITHOUT NDEBUG and runs everything through them:
#   1. rig      : `assert-rig` (Tests/AssertRig.lean) performs a deliberately out-of-range
#                 proof-carrying read; it must abort with LEAN ASSERTION VIOLATION (SIGABRT, 134),
#                 its `control` mode must not (expected-failure subprocess).
#   2. suites   : `tests` (every registered suite, including the worker suites, which run the
#                 assertions-built `worker`/`worker-probe`).
#   3. fuzz     : `scripts/fuzz.sh smoke` and `scripts/fuzz.sh long` (the long profile capped by
#                 FUZZ_LONG_SECONDS, default 90 here).
#   4. adversarial : `inspect` text and raster views over Tests/adversarial/*.pdf and
#                 Tests/adversarial/encrypted/*.pdf (the bomb files are covered by the `bombs`
#                 suite; the long-structure files of task 13.5 are picked up when they land).
#   5. pinned   : the same two views over the pinned corpus (scripts/corpus/pinned.txt; fetched
#                 and SHA-256-verified by scripts/corpus/pinned.py when missing).
# Exit status 0 only when every stage passed and the number of assertion failures is 0; the summary
# (commit, counts per stage, assertion failures, rig abort) goes to stdout, to
# <work>/summary.txt and, in CI, to $GITHUB_STEP_SUMMARY.
#
# Usage: scripts/asserts.sh [--work DIR] [--jobs N] [--no-corpus] [--skip-build]
#   --work DIR     the separate workspace (default <repo>/.lake/asserts-ws, git-ignored)
#   --jobs N       parallel inspector runs in stages 4-5 (default 4)
#   --no-corpus    skip stage 5 (no network, no corpus/files)
#   --skip-build   reuse the build of an earlier run in --work (sources are still re-copied)
# Environment: FUZZ_LONG_SECONDS (default 90), ASSERTS_FILE_TIMEOUT (seconds per inspector run,
# default 600), ASSERTS_SUITES_TIMEOUT (seconds for the suites, default 2400).
#
# HOW THE SEPARATION WORKS. The assertions build lives in its own workspace, a copy of the tracked
# sources (plus untracked, non-ignored ones) with its own `.lake`, so the release build in the
# repository is never touched: Lake caches the elaborated lakefile together with its `-K`
# options and reuses them on later calls without `-K`, so `-Kasserts=1` must never run in the
# release workspace. The copy also keeps the hard-coded `.lake/build/bin/worker` paths of the
# worker suites pointing at the assertions-built executables. lakefile.lean's `-Kasserts=1`
# (`assertsBuild`) adds `-UNDEBUG` to this package's C flags; the `jpeg2000` dependency's flags
# are not ours to set, so the script also sets clang's CCC_OVERRIDE_OPTIONS (rewrites `-DNDEBUG`
# to `-UNDEBUG` in every compile of the build, hence the `### CCC_OVERRIDE_OPTIONS` noise in the
# build log). The build is then checked: objects of both packages must reference
# `lean_notify_assert` (the symbol an enabled assert compiles to), and the compile flags are
# probed.
#
# WHAT IS COVERED. Only the generated C and the inline functions of lean.h (array, byte array,
# constructor field accessors, ...). The prebuilt Lean runtime library (libleanshared, libInit,
# libStd, libLean) stays a release build: its internal asserts are not enabled. docs/safety.md
# says so (task 13.21).
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo="$(dirname "$here")"
work="$repo/.lake/asserts-ws"
jobs=4
do_corpus=1
do_build=1
while [ $# -gt 0 ]; do
  case "$1" in
    --work) work="${2:?--work needs a directory}"; shift 2 ;;
    --jobs) jobs="${2:?--jobs needs a number}"; shift 2 ;;
    --no-corpus) do_corpus=0; shift ;;
    --skip-build) do_build=0; shift ;;
    -h|--help) sed -n '2,45p' "$0"; exit 0 ;;
    *) echo "usage: $0 [--work DIR] [--jobs N] [--no-corpus] [--skip-build]" >&2; exit 2 ;;
  esac
done
fuzz_long_seconds="${FUZZ_LONG_SECONDS:-90}"
file_timeout="${ASSERTS_FILE_TIMEOUT:-600}"
suites_timeout="${ASSERTS_SUITES_TIMEOUT:-2400}"

mkdir -p "$work"
work="$(cd "$work" && pwd)"
logs="$work/logs"
mkdir -p "$logs"
t_start=$(date +%s)
failures=0            # stages that failed
assert_failures=0     # assertion violations or aborts seen anywhere
declare -a lines=()   # summary lines

note() { printf '%s\n' "$*"; }
stage_fail() { failures=$((failures + 1)); note "FAIL: $*"; }
elapsed() { echo $(( $(date +%s) - t_start )); }

# Count assertion violations in the given log files (the runtime prints this on a failed assert).
count_violations() { cat "$@" 2>/dev/null | grep -c 'ASSERTION VIOLATION' || true; }

commit="$(git -C "$repo" rev-parse HEAD 2>/dev/null || echo unknown)"
if [ -n "$(git -C "$repo" status --porcelain 2>/dev/null)" ]; then commit="$commit (+ uncommitted changes)"; fi

# ---------------------------------------------------------------------------------- workspace
note "== asserts: workspace $work"
tar_list="$work/.sources.list"
(cd "$repo" && git ls-files -z -co --exclude-standard) > "$tar_list"
# The copy is re-made on every run (Lake keys on content hashes, so unchanged files do not
# rebuild); files removed from the repository must disappear from the copy.
for d in SafePdf Tests examples scripts c docs macos; do rm -rf "${work:?}/$d"; done
(cd "$repo" && tar --null --ignore-failed-read -T "$tar_list" -cf -) 2>/dev/null | tar -xf - -C "$work" || true
for f in lakefile.lean lake-manifest.json lean-toolchain SafePdf.lean; do
  [ -e "$work/$f" ] || { echo "asserts: $f missing in the copy" >&2; exit 2; }
done
# The dependency checkout is reused from the release workspace when present (no network); its
# build products are not copied.
if [ ! -d "$work/.lake/packages/jpeg2000" ] && [ -d "$repo/.lake/packages/jpeg2000" ]; then
  mkdir -p "$work/.lake/packages"
  cp -a "$repo/.lake/packages/jpeg2000" "$work/.lake/packages/jpeg2000"
  rm -rf "$work/.lake/packages/jpeg2000/.lake/build"
fi
# Corpus files stay in the repository (verified there); the copy sees them through a link.
mkdir -p "$work/corpus"
if [ "$do_corpus" = 1 ]; then
  python3 -I "$repo/scripts/corpus/pinned.py" --fetch > "$logs/pinned-fetch.log" 2>&1 \
    || { cat "$logs/pinned-fetch.log"; stage_fail "pinned corpus fetch/verification"; do_corpus=0; }
fi
mkdir -p "$repo/corpus/files"
rm -rf "$work/corpus/files"
ln -s "$repo/corpus/files" "$work/corpus/files"

# ------------------------------------------------------------------------------------- build
# Rewrites -DNDEBUG to -UNDEBUG in every clang invocation of the build (covers the jpeg2000
# dependency too). Exported for the whole script, so every `lake` call below keeps the flags.
export CCC_OVERRIDE_OPTIONS='s/^-DNDEBUG$/-UNDEBUG/'
probe_flags="$(echo | leanc -O3 -DNDEBUG -E -dM -x c - 2>/dev/null | grep -c '^#define NDEBUG' || true)"
if [ "$probe_flags" != 0 ]; then
  stage_fail "CCC_OVERRIDE_OPTIONS did not remove NDEBUG from a probe compile"
fi

targets=(tests fuzz inspect worker worker-probe assert-rig)
if [ "$do_build" = 1 ]; then
  note "== asserts: building ${targets[*]} without NDEBUG (separate workspace, first build takes minutes)"
  if (cd "$work" && lake build -R -Kasserts=1 "${targets[@]}") > "$logs/build.log" 2>&1; then
    note "build: ok ($(grep -c '^✔\|^ℹ\|^⚠' "$logs/build.log" || true) job lines, log $logs/build.log)"
  else
    grep -v '^###' "$logs/build.log" | tail -40
    stage_fail "assertions build"
    exit 1
  fi
fi
bin="$work/.lake/build/bin"
for t in tests fuzz inspect worker worker-probe assert-rig; do
  [ -x "$bin/$t" ] || { stage_fail "$bin/$t not built"; }
done

# Build check: objects that reference lean_notify_assert, per package. A release object never
# does. `grep -a` finds the symbol name in the object's string table; no nm needed.
asserted_objects() { # dir -> "with/total"
  local dir="$1" total=0 with=0 f
  while IFS= read -r -d '' f; do
    total=$((total + 1))
    if grep -qa 'lean_notify_assert' "$f"; then with=$((with + 1)); fi
  done < <(find "$dir" -type f \( -name '*.o' -o -name '*.o.export' -o -name '*.o.noexport' \) -print0 2>/dev/null)
  echo "$with/$total"
}
own="$(asserted_objects "$work/.lake/build/ir")"
dep="$(asserted_objects "$work/.lake/packages/jpeg2000/.lake/build/ir")"
rel="n/a"
if [ -d "$repo/.lake/build/ir" ]; then rel="$(asserted_objects "$repo/.lake/build/ir")"; fi
note "objects referencing lean_notify_assert: safe-pdf $own, jpeg2000 $dep (release build in the repository: $rel)"
[ "${own%%/*}" -gt 0 ] || stage_fail "no safe-pdf object references lean_notify_assert (NDEBUG still on?)"
[ "${dep%%/*}" -gt 0 ] || stage_fail "no jpeg2000 object references lean_notify_assert (NDEBUG still on?)"
lines+=("build        : tests fuzz inspect worker worker-probe assert-rig; objects with live asserts: safe-pdf $own, jpeg2000 $dep (release: $rel)")

# --------------------------------------------------------------------------------- 1. rig
note "== asserts: rig self-test (expected-failure subprocess)"
rig_ok=1
if [ -x "$bin/assert-rig" ]; then
  if out="$(cd "$work" && timeout 60 "$bin/assert-rig" control 2>&1)" && [[ "$out" == *"control ok"* ]]; then
    note "rig control: ok ($out)"
  else
    note "rig control: FAILED ($out)"; rig_ok=0
  fi
  rig_aborts=0
  for mode in array bytes; do
    set +e
    (cd "$work" && timeout 60 "$bin/assert-rig" "$mode") > "$logs/rig-$mode.log" 2>&1
    st=$?
    set -e
    if [ "$st" = 134 ] && grep -q 'ASSERTION VIOLATION' "$logs/rig-$mode.log"; then
      rig_aborts=$((rig_aborts + 1))
      note "rig $mode: aborted as required (exit 134): $(grep -m1 -A3 'ASSERTION VIOLATION' "$logs/rig-$mode.log" | tr '\n' ' ')"
    else
      note "rig $mode: DID NOT ABORT (exit $st): $(tr '\n' ' ' < "$logs/rig-$mode.log")"; rig_ok=0
    fi
  done
else
  rig_ok=0; rig_aborts=0
fi
if [ "$rig_ok" = 1 ]; then
  lines+=("rig          : control ok; out-of-range Array read and ByteArray read aborted with LEAN ASSERTION VIOLATION (exit 134), $rig_aborts/2")
else
  stage_fail "rig self-test (the assertions build does not abort on an out-of-range proof-carrying read)"
  lines+=("rig          : FAILED")
fi

# Run a stage command in the workspace; echo its status. Aborts (134), segfaults (139) and
# the runtime's assertion message count as assertion failures.
status_is_crash() { [ "$1" = 134 ] || [ "$1" = 139 ] || [ "$1" = 132 ] || [ "$1" = 136 ] || [ "$1" = 138 ]; }

# -------------------------------------------------------------------------------- 2. suites
note "== asserts: test suites (timeout ${suites_timeout}s)"
set +e
(cd "$work" && timeout "$suites_timeout" "$bin/tests") > "$logs/tests.log" 2>&1
st=$?
set -e
pass=$(grep -c '^\[PASS\]' "$logs/tests.log" || true)
fail=$(grep -c '^\[FAIL\]' "$logs/tests.log" || true)
v=$(count_violations "$logs/tests.log")
status_is_crash "$st" && v=$((v > 0 ? v : 1))
assert_failures=$((assert_failures + v))
note "suites: $pass passed, $fail failed, exit $st, assertion violations $v"
if [ "$st" != 0 ] || [ "$fail" != 0 ] || [ "$pass" = 0 ]; then
  grep -v '^\[PASS\]' "$logs/tests.log" | tail -30
  stage_fail "test suites (exit $st)"
fi
lines+=("suites       : $pass passed, $fail failed (exit $st), assertion violations $v")

# ---------------------------------------------------------------------------------- 3. fuzz
# scripts/fuzz.sh of the copy: it runs `lake build fuzz` and `lake exe fuzz` there, i.e. on the
# assertions build (the copy's cached lakefile carries -Kasserts=1; CCC_OVERRIDE_OPTIONS is exported).
fuzz_summary() { { grep -E '^fuzz: time limit' "$1" || true; grep -E '^fuzz: summary:' "$1" | tail -1; } | sed 's/^fuzz: //' | tr '\n' ';'; }
for profile in smoke long; do
  note "== asserts: fuzz $profile"
  set +e
  (cd "$work" && FUZZ_LONG_SECONDS="$fuzz_long_seconds" timeout 1800 scripts/fuzz.sh "$profile") > "$logs/fuzz-$profile.log" 2>&1
  st=$?
  set -e
  v=$(count_violations "$logs/fuzz-$profile.log")
  status_is_crash "$st" && v=$((v > 0 ? v : 1))
  assert_failures=$((assert_failures + v))
  note "fuzz $profile: exit $st, assertion violations $v, $(fuzz_summary "$logs/fuzz-$profile.log")"
  if [ "$st" != 0 ]; then tail -20 "$logs/fuzz-$profile.log"; stage_fail "fuzz $profile (exit $st)"; fi
  lines+=("fuzz $profile$( [ "$profile" = smoke ] && echo '   ' || echo '    ')  : exit $st, assertion violations $v; $(fuzz_summary "$logs/fuzz-$profile.log")")
done

# --------------------------------------------------------------------- 4./5. inspector runs
# One inspector run per file and view; results go to $dir/<n>.res as `status<TAB>view<TAB>file`.
# Status 0 (opens) and 1 (parse error, e.g. adversarial files that must be rejected) are fine;
# 2 (I/O or usage), a timeout (124) or a crash (134, 139, ...) is a failure.
run_files() { # name file...
  local name="$1"; shift
  local dir="$logs/$name"
  rm -rf "$dir"; mkdir -p "$dir"
  export bin work dir file_timeout
  printf '%s\0' "$@" | xargs -0 -P "$jobs" -I{} bash -c '
    f="$1"; base="$(basename "$f")"
    for view in text raster; do
      log="$dir/$base.$view.log"
      set +e
      (cd "$work" && timeout "$file_timeout" "$bin/inspect" --view "$view" "$f") > "$log" 2>&1
      st=$?
      printf "%s\t%s\t%s\n" "$st" "$view" "$f" > "$dir/$base.$view.res"
    done' _ {}
  local ok=0 rej=0 bad=0 res st
  for res in "$dir"/*.res; do
    [ -e "$res" ] || continue
    st="$(cut -f1 "$res")"
    case "$st" in
      0) ok=$((ok + 1)) ;;
      1) rej=$((rej + 1)) ;;
      *) bad=$((bad + 1)); note "  BAD: exit $st: $(cut -f2,3 "$res" | tr '\t' ' ')"
         status_is_crash "$st" && assert_failures=$((assert_failures + 1)) ;;
    esac
  done
  local v; v=$(count_violations "$dir"/*.log)
  assert_failures=$((assert_failures + v))
  # Pages seen: the raster view prints `total: N page(s) rendered, F failed ...`, the text view
  # `--- page N:` per page.
  RUN_RASTER=$(cat "$dir"/*.raster.log 2>/dev/null \
    | sed -n 's/^total: *\([0-9][0-9]*\) page(s) rendered, \([0-9][0-9]*\) failed.*/\1 \2/p' \
    | awk '{r += $1; f += $2} END {printf "%d pages rendered (%d page errors)", r, f}')
  RUN_TEXT=$(cat "$dir"/*.text.log 2>/dev/null | grep -c '^--- page [0-9]' || true)
  RUN_OK=$ok RUN_REJ=$rej RUN_BAD=$bad RUN_V=$v RUN_N=$#
}

note "== asserts: adversarial files through text and raster"
shopt -s nullglob
adv=("$work"/Tests/adversarial/*.pdf "$work"/Tests/adversarial/encrypted/*.pdf)
shopt -u nullglob
if [ ${#adv[@]} -eq 0 ]; then stage_fail "no adversarial files found"; else
  run_files adversarial "${adv[@]}"
  note "adversarial: ${RUN_N} files x 2 views: $RUN_OK opened, $RUN_REJ rejected, $RUN_BAD bad, assertion violations $RUN_V"
  [ "$RUN_BAD" = 0 ] && [ "$RUN_V" = 0 ] || stage_fail "adversarial files"
  lines+=("adversarial  : $RUN_N files x {text, raster}: $RUN_OK opened, $RUN_REJ rejected (exit 1), $RUN_BAD bad; $RUN_TEXT text pages, $RUN_RASTER; assertion violations $RUN_V")
fi

if [ "$do_corpus" = 1 ]; then
  note "== asserts: pinned corpus through text and raster"
  # --paths prints paths relative to the repository root (corpus/files/...); the workspace's
  # corpus/files is a link to the repository's.
  mapfile -t pinned < <(python3 -I "$repo/scripts/corpus/pinned.py" --paths 2>/dev/null | sed "s#^#$work/#")
  if [ ${#pinned[@]} -eq 0 ]; then stage_fail "no pinned corpus files"; else
    run_files pinned "${pinned[@]}"
    note "pinned corpus: ${RUN_N} files x 2 views: $RUN_OK opened, $RUN_REJ rejected, $RUN_BAD bad, assertion violations $RUN_V"
    [ "$RUN_BAD" = 0 ] && [ "$RUN_V" = 0 ] || stage_fail "pinned corpus"
    lines+=("pinned corpus: $RUN_N files x {text, raster}: $RUN_OK opened, $RUN_REJ rejected, $RUN_BAD bad; $RUN_TEXT text pages, $RUN_RASTER; assertion violations $RUN_V")
  fi
else
  lines+=("pinned corpus: skipped")
fi

# -------------------------------------------------------------------------------- summary
[ "$assert_failures" = 0 ] || failures=$((failures + 1))
{
  echo "## Assertions build (task 13.10)"
  echo
  echo "commit            : $commit"
  echo "toolchain         : $(cat "$repo/lean-toolchain" 2>/dev/null)"
  echo "C flags           : -O3 without NDEBUG (lakefile -Kasserts=1 + CCC_OVERRIDE_OPTIONS for the dependency)"
  echo "not covered       : the prebuilt Lean runtime library (release build); generated C and lean.h inline functions only"
  for l in "${lines[@]}"; do echo "$l"; done
  echo "assertion failures: $assert_failures"
  echo "failed stages     : $failures"
  echo "wall time         : $(elapsed) s"
  if [ "$failures" = 0 ]; then echo "result            : PASS"; else echo "result            : FAIL"; fi
} > "$work/summary.txt"
echo
cat "$work/summary.txt"
if [ -n "${GITHUB_STEP_SUMMARY:-}" ]; then { echo '```'; cat "$work/summary.txt"; echo '```'; } >> "$GITHUB_STEP_SUMMARY"; fi
[ "$failures" = 0 ]
