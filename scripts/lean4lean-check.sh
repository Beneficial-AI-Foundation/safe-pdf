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
# Steps: fetch + verify + unpack -> `lake -d … build l4lexact` (our exact-name driver over
# lean4lean's Replay, not its metatheory) -> `lake env <driver> FUEL M` for every built module M equal
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

[[lean_exe]]
name = "l4lexact"
root = "ExactMain"
supportInterpreter = true
EOF
# Our own driver (upstream Main.lean selects modules by name *prefix* and replays the matches
# on parallel task threads with Lean's fixed default thread stack). This one replays exactly
# the module names given, one after another on the main thread, whose stack `ulimit -s`
# controls. It calls the same Lean4Lean.Replay.replayFromImports; the check is unchanged.
cat >"$src/lean4lean/ExactMain.lean" <<'EOF'
import Lean4Lean.Replay

open Lean hiding Environment Exception
open Lean4Lean.Replay

/-- `--config:field=value` flags overlaid on the default `FuelConfig` through its JSON form. -/
def fuelOfFlags (flags : List String) : IO Lean4Lean.FuelConfig := do
  let mut obj := match Lean.toJson (({} : Lean4Lean.FuelConfig)) with
    | .obj m => m
    | _ => Std.TreeMap.Raw.empty
  for flag in flags do
    let some rest := flag.dropPrefix? "--config:"
      | throw <| IO.userError s!"unknown flag {flag}"
    let [field, value] := rest.toString.splitOn "="
      | throw <| IO.userError s!"malformed flag {flag}"
    unless obj.contains field do throw <| IO.userError s!"unknown fuel field {field}"
    match Lean.Json.parse value with
    | .ok j => obj := obj.insert field j
    | .error _ => throw <| IO.userError s!"bad value in {flag}"
  IO.ofExcept (Lean.fromJson? (.obj obj))

/-- Replay exactly the given modules (no prefix matching), sequentially, on this thread. -/
unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let (flags, mods) := args.partition fun s => s.startsWith "-"
  let fuel ← fuelOfFlags flags
  let mut n := 0
  let mut err := false
  for arg in mods do
    let m := arg.toName
    if m.isAnonymous then throw <| IO.userError s!"Could not resolve module: {arg}"
    try
      n := n + (← replayFromImports m (fuel := fuel))
    catch e =>
      IO.eprintln s!"lean4lean found a problem in {m}:\n{e.toString}"
      err := true
  if err then return 1
  println! "checked {n} declarations"
  return 0
EOF
printf '%s\n' "$L4L_TOOLCHAIN" >"$src/lean4lean/lean-toolchain"
printf '%s\n' "$L4L_TOOLCHAIN" >"$src/batteries/lean-toolchain"

if [ "$fetch_only" = 1 ]; then
  echo "lean4lean-check: verified and unpacked into $src (--fetch-only: nothing built)"
  exit 0
fi

echo "lean4lean-check: building the checker (lake -d $src/lean4lean build l4lexact)"
lake -d "$src/lean4lean" build l4lexact
checker="$src/lean4lean/.lake/build/bin/l4lexact"
[ -x "$checker" ] || { echo "lean4lean-check: $checker not built" >&2; exit 1; }

# Module selection. Upstream lean4lean matches each MODULE argument as a name *prefix* and
# replays all matches on parallel tasks, so a parent such as SafePdf.Core.Crypt (Crypt.lean
# beside Crypt/) could not be checked alone; on Linux CI those prefix runs crashed every time
# (SIGSEGV: SafePdf.Core.Crypt, .Doc, .Xref, .Filter; 127 other modules passed) and macOS
# crashed intermittently. Here every built module equal to or under each MODULE is listed
# from the .olean tree and checked by *exact* name with our own driver (ExactMain.lean
# above), one process per module, so a parent module is checked on its own declarations and
# its submodules in their own runs.
mods=()
for m in "${modules[@]}"; do
  rel="$(printf '%s' "$m" | tr . /)"
  if [ -f ".lake/build/lib/lean/$rel.olean" ]; then
    mods+=("$m")
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

# Stack. lean4lean's recursion is bounded by fuel (below), not by the native stack, and the
# raised recDepth lets it recurse far deeper than 8 MiB of stack holds. The driver runs on
# the main thread, whose stack is the process limit, so raise it (hard limit permitting).
ulimit -s unlimited 2>/dev/null || ulimit -s "$(ulimit -H -s)" 2>/dev/null || true
echo "lean4lean-check: stack limit: $(ulimit -s)"

# Time limits: L4L_MODULE_TIMEOUT seconds per run (default 1200, enforced when `timeout` or
# `gtimeout` exists) and L4L_TOTAL_TIMEOUT seconds for the whole script (default 2700; no
# further module is started after it, and the script then fails with a TIMEOUT line).
tmo=""
for c in timeout gtimeout; do
  if command -v "$c" >/dev/null; then tmo="$c"; break; fi
done
mod_limit="${L4L_MODULE_TIMEOUT:-1200}" total_limit="${L4L_TOTAL_TIMEOUT:-2700}"
t0=$(date +%s)

# Fuel: lean4lean bounds its recursion and unfolding by FuelConfig (Lean4Lean/FuelConfig.lean)
# instead of the native stack; its defaults are below what some of our definitions need
# (e.g. "deep recursion" on SafePdf.Core.Filter.Ascii.a85Spec_encode._f at recDepth 50000).
# Raising fuel only lets the checker run longer; it does not accept anything it would reject.
read -r -a fuel <<<"${L4L_FUEL:---config:recDepth=1000000 --config:whnf=10000000 --config:whnfEager=100000000 --config:lazyDelta=1000000}"

echo "lean4lean-check: re-checking ${#mods[@]} module(s), exact names, fuel: ${fuel[*]}"
# Outcomes, labelled apart: ok; FAIL = the kernel rejected a declaration (a real proof
# problem); CRASH / TIMEOUT = the tool died or ran out of time (a tool problem, but still a
# failure: the module is then not re-checked). Crashes are retried (L4L_RETRIES, default 3).
status=0 failed=() crashed=() timedout=() skipped=()
retries="${L4L_RETRIES:-3}"
for m in "${mods[@]}"; do
  if [ $(( $(date +%s) - t0 )) -ge "$total_limit" ]; then
    skipped+=("$m")
    continue
  fi
  try=1
  while :; do
    start=$(date +%s)
    set +e
    out="$(lake env ${tmo:+$tmo "$mod_limit"} "$checker" "${fuel[@]}" "$m" 2>&1)"
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
    continue
  fi
  printf '%s\n' "$out" | tail -n 20 >&2
  if [ "$rc" = 124 ] && [ -n "$tmo" ]; then
    echo "TIMEOUT $m (over ${mod_limit} s; tool problem, not a kernel rejection)"
    timedout+=("$m")
  elif [ "$rc" -ge 128 ]; then
    echo "CRASH  $m (exit $rc, signal $((rc - 128)); ${secs} s, after $try tries; tool crash, not a kernel rejection)"
    crashed+=("$m")
  else
    echo "FAIL   $m (exit $rc; ${secs} s; kernel rejection or driver error)"
    failed+=("$m")
  fi
  status=1
done
if [ ${#skipped[@]} -gt 0 ]; then
  echo "TIMEOUT overall limit ${total_limit} s reached; not checked: ${skipped[*]}"
  status=1
fi
echo "lean4lean-check: ${#mods[@]} module(s): ${#failed[@]} rejected/failed${failed[*]:+: ${failed[*]}}; ${#crashed[@]} crashed${crashed[*]:+: ${crashed[*]}}; ${#timedout[@]} timed out${timedout[*]:+: ${timedout[*]}}; ${#skipped[@]} not run"
exit $status
