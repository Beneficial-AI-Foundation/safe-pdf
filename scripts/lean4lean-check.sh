#!/usr/bin/env bash
# Re-check the project's .olean files with lean4lean (task 12.6; Plan.md §6 Phase 12
# "Independent verification"; docs/safety.md §5 item 5). Run from the repo root after
# `lake build`.
#
#   scripts/lean4lean-check.sh [--work DIR] [--fetch-only] [--strict] [MODULE ...]
#
# lean4lean (github.com/digama0/lean4lean) is a Lean 4 kernel written in Lean. It replays
# every declaration of the given modules from their .olean files into a fresh kernel
# environment and type-checks it again. Its README says it is derived from the C++ kernel and
# may share its bugs, so it is a second implementation, not an independent theory; still, it
# re-checks our proofs without trusting the elaborator, the tactic framework or the .olean
# writer, and it is the only such checker for our toolchain.
#
# Pinned version (no lean4lean release tags exist; branch `master` at this commit declares
# toolchain leanprover/lean4:v4.36.0, the project's own):
#   lean4lean  commit 23fd0341e823a332ce5df21a1897c8afcbf34471, GitHub source tarball
#              SHA-256 eddc426e433c9acebc7dd811d7869a10bd07a212d3e87beab349ecd451a9d57e
#   batteries  commit b4b25a3886a16daacaf6615c2eea7170a6e8f458 (tag v4.36.0, from lean4lean's
#              lake-manifest.json), GitHub source tarball
#              SHA-256 dfb91e30d8a0f7665d3b7c1ca7ffcae70e973d35a6a6cea09a913589a64fd016
# (The tarball hashes were computed on 2026-11-23. GitHub's generated archives have been
# stable in practice but are not guaranteed to be; a mismatch makes this script fail closed.)
#
# Untrusted-download rules (CLAUDE.md, wave ground rule 8): both archives go into a fresh
# directory under --work (default: a new temp dir), are verified by SHA-256 before they are
# unpacked, and nothing is run from inside them: lean4lean's Lake configuration is replaced
# by one written here (the same targets, with batteries as a local path dependency, so Lake
# clones nothing), Lake is driven with `lake -d DIR` from the repo root, and the checker
# binary runs with the repo root as working directory under `lake env`.
#
# Steps: fetch + verify + unpack -> `lake -d … build lean4lean` (the checker exe only, not
# lean4lean's own metatheory) -> `lake env <checker> FUEL M` for every built module M equal
# to or under each MODULE (default: SafePdf, i.e. SafePdf and every SafePdf.*; the oleans
# must be built), one process per module. FUEL defaults to raised lean4lean fuel limits
# (see below); override with the environment variable L4L_FUEL.
#
# --work DIR    working directory for downloads and the lean4lean build (kept afterwards;
#               default: a temp dir, removed at the end).
# --fetch-only  stop after verifying and unpacking (no build, nothing executed).
# --strict      treat "skip" conditions (toolchain mismatch, missing tools) as failures.
# Exit status: 0 when every module re-checks (or the check is skipped without --strict),
# 1 when lean4lean reports a problem or a download fails verification, 2 on usage errors.
set -euo pipefail

L4L_REV=23fd0341e823a332ce5df21a1897c8afcbf34471
L4L_SHA256=eddc426e433c9acebc7dd811d7869a10bd07a212d3e87beab349ecd451a9d57e
L4L_TOOLCHAIN=leanprover/lean4:v4.36.0
BAT_REV=b4b25a3886a16daacaf6615c2eea7170a6e8f458
BAT_SHA256=dfb91e30d8a0f7665d3b7c1ca7ffcae70e973d35a6a6cea09a913589a64fd016

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo="$(dirname "$here")"
cd "$repo"

work="" fetch_only=0 strict=0
modules=()
while [ $# -gt 0 ]; do
  case "$1" in
    --work) work="${2:?--work needs a directory}"; shift ;;
    --fetch-only) fetch_only=1 ;;
    --strict) strict=1 ;;
    -h|--help) sed -n '2,43p' "$0"; exit 0 ;;
    -*) echo "usage: $0 [--work DIR] [--fetch-only] [--strict] [MODULE ...]" >&2; exit 2 ;;
    *) modules+=("$1") ;;
  esac
  shift
done
[ ${#modules[@]} -gt 0 ] || modules=(SafePdf)

skip() {  # skip MESSAGE: a condition under which the check cannot run on this machine
  echo "lean4lean-check: SKIPPED: $1" >&2
  if [ "$strict" = 1 ]; then exit 1; fi
  exit 0
}

ours="$(tr -d '[:space:]' < lean-toolchain)"
if [ "$ours" != "$L4L_TOOLCHAIN" ]; then
  skip "the project's toolchain is $ours but the pinned lean4lean commit ${L4L_REV:0:12} targets $L4L_TOOLCHAIN. Pin a lean4lean commit whose lean-toolchain is $ours (branch master or arena-<version> of github.com/digama0/lean4lean) and update L4L_REV, L4L_SHA256 and the batteries pin from its lake-manifest.json."
fi
for t in curl tar lake; do
  command -v "$t" >/dev/null || skip "$t not found"
done
if command -v sha256sum >/dev/null; then
  sha256() { sha256sum "$1" | cut -d' ' -f1; }
elif command -v shasum >/dev/null; then
  sha256() { shasum -a 256 "$1" | cut -d' ' -f1; }
else
  skip "neither sha256sum nor shasum found"
fi

if [ -z "$work" ]; then
  work="$(mktemp -d)"
  trap 'rm -rf "$work"' EXIT
else
  mkdir -p "$work"
  work="$(cd "$work" && pwd)"
fi
dl="$work/download"
src="$work/src"
# Fresh directories every run: never reuse an unpacked tree that could have been altered.
rm -rf "$dl" "$src"
mkdir -p "$dl" "$src"

fetch() {  # fetch OWNER/REPO REV SHA256 NAME
  local url="https://codeload.github.com/$1/tar.gz/$2" out="$dl/$4.tar.gz" got
  echo "lean4lean-check: fetching $1 @ ${2:0:12}"
  curl -sSfL --max-time 300 --max-filesize 104857600 -o "$out" "$url"
  got="$(sha256 "$out")"
  if [ "$got" != "$3" ]; then
    echo "lean4lean-check: SHA-256 mismatch for $1 @ $2: expected $3, got $got" >&2
    rm -f "$out"
    exit 1
  fi
  mkdir -p "$src/$4"
  # GitHub archives hold one top-level directory <repo>-<rev>/; strip it. No absolute or
  # parent paths are accepted (tar refuses them by default; checked again below).
  if tar -tzf "$out" | grep -Eq '(^/|(^|/)\.\.(/|$))'; then
    echo "lean4lean-check: $1 archive holds absolute or .. paths; refusing" >&2
    exit 1
  fi
  tar -xzf "$out" -C "$src/$4" --strip-components=1
}

fetch digama0/lean4lean "$L4L_REV" "$L4L_SHA256" lean4lean
fetch leanprover-community/batteries "$BAT_REV" "$BAT_SHA256" batteries

got_tc="$(tr -d '[:space:]' < "$src/lean4lean/lean-toolchain")"
if [ "$got_tc" != "$L4L_TOOLCHAIN" ]; then
  echo "lean4lean-check: verified archive declares $got_tc, expected $L4L_TOOLCHAIN" >&2
  exit 1
fi

# Our own Lake configuration for the checker: lean4lean's targets that `lean4lean` (the exe)
# needs, batteries as a path dependency (no git clone), the pinned toolchain.
rm -f "$src/lean4lean/lakefile.lean" "$src/lean4lean/lakefile.toml" "$src/lean4lean/lake-manifest.json"
cat >"$src/lean4lean/lakefile.toml" <<EOF
# Written by safe-pdf scripts/lean4lean-check.sh (replaces the upstream configuration).
name = "lean4lean"

[[require]]
name = "batteries"
path = "../batteries"

[[lean_lib]]
name = "Lean4Lean"

[[lean_exe]]
name = "lean4lean"
root = "Main"
supportInterpreter = true
EOF
printf '%s\n' "$L4L_TOOLCHAIN" >"$src/lean4lean/lean-toolchain"
printf '%s\n' "$L4L_TOOLCHAIN" >"$src/batteries/lean-toolchain"

if [ "$fetch_only" = 1 ]; then
  echo "lean4lean-check: verified and unpacked into $src (--fetch-only: nothing built)"
  exit 0
fi

echo "lean4lean-check: building the checker (lake -d $src/lean4lean build lean4lean)"
lake -d "$src/lean4lean" build lean4lean
checker="$src/lean4lean/.lake/build/bin/lean4lean"
[ -x "$checker" ] || { echo "lean4lean-check: $checker not built" >&2; exit 1; }

# One checker process per module, serially. lean4lean matches MODULE as a *prefix* and checks
# several matches on parallel tasks; in that mode it crashed with SIGSEGV intermittently
# (2026-11-23, macOS arm64: `SafePdf.Core.Crypt`, which also matches its four submodules,
# 3 runs in 6), while 6 of 6 runs of each single submodule passed. A module that has
# submodules (Crypt.lean next to Crypt/) cannot be checked alone, so such runs are retried
# on a crash (L4L_RETRIES, default 8); its submodules also get their own runs. A parent
# whose source holds only imports and comments (the umbrella SafePdf.lean) declares nothing,
# so it is skipped: its prefix run would be every module at once in parallel.
imports_only() {  # imports_only FILE.lean: true when FILE has no line but imports/comments
  python3 -I -c '
import re, sys
s = re.sub(r"/-.*?-/", "", open(sys.argv[1], encoding="utf-8").read(), flags=re.S)
s = re.sub(r"--[^\n]*", "", s)
sys.exit(0 if all(not l.strip() or l.startswith("import ") for l in s.splitlines()) else 1)
' "$1"
}
mods=()
for m in "${modules[@]}"; do
  rel="$(printf '%s' "$m" | tr . /)"
  if [ -f ".lake/build/lib/lean/$rel.olean" ]; then
    if [ -d ".lake/build/lib/lean/$rel" ] && [ -f "$rel.lean" ] && imports_only "$rel.lean"; then
      echo "skip   $m (imports only; its submodules are checked one by one)"
    else
      mods+=("$m")
    fi
  fi
  if [ -d ".lake/build/lib/lean/$rel" ]; then
    while IFS= read -r f; do
      f="${f#.lake/build/lib/lean/}"
      f="${f%.olean}"
      mods+=("$(printf '%s' "$f" | tr / .)")
    done < <(find ".lake/build/lib/lean/$rel" -name '*.olean' | LC_ALL=C sort)
  fi
done
if [ ${#mods[@]} -eq 0 ]; then
  echo "lean4lean-check: no built .olean for ${modules[*]} (run lake build first)" >&2
  exit 1
fi

# Fuel: lean4lean bounds its recursion and unfolding by FuelConfig (Lean4Lean/FuelConfig.lean)
# instead of the native stack; its defaults are below what some of our definitions need
# (e.g. "deep recursion" on SafePdf.Core.Filter.Ascii.a85Spec_encode._f at recDepth 50000).
# Raising fuel only lets the checker run longer; it does not accept anything it would reject.
read -r -a fuel <<<"${L4L_FUEL:---config:recDepth=1000000 --config:whnf=10000000 --config:whnfEager=100000000 --config:lazyDelta=1000000}"

echo "lean4lean-check: re-checking ${#mods[@]} module(s), fuel: ${fuel[*]}"
status=0 failed=()
retries="${L4L_RETRIES:-8}"
for m in "${mods[@]}"; do
  try=1
  while :; do
    start=$(date +%s)
    set +e
    out="$(lake env "$checker" "${fuel[@]}" "$m" 2>&1)"
    rc=$?
    set -e
    secs=$(( $(date +%s) - start ))
    if [ "$rc" -ge 128 ] && [ "$try" -lt "$retries" ]; then
      echo "crash  $m (exit $rc, signal $((rc - 128)); try $try of $retries, retrying)"
      try=$((try + 1))
      continue
    fi
    break
  done
  if [ "$rc" = 0 ]; then
    echo "ok     $m (${secs} s) $(printf '%s\n' "$out" | tail -n 1)"
  else
    printf '%s\n' "$out" | tail -n 20 >&2
    if [ "$rc" -ge 128 ]; then
      echo "CRASH  $m (exit $rc, signal $((rc - 128)); ${secs} s, after $try tries)"
    else
      echo "FAIL   $m (exit $rc; ${secs} s)"
    fi
    failed+=("$m")
    status=1
  fi
done
echo "lean4lean-check: ${#mods[@]} module(s), ${#failed[@]} failed${failed[*]:+: ${failed[*]}}"
exit $status
