#!/usr/bin/env bash
# Compiled-vs-interpreted differential over the test suites (task 12.6; Plan.md §6 Phase 12
# "Independent verification"; docs/safety.md §5 item 6). Run from the repo root.
#
#   scripts/compiled-vs-interpreted.sh [--no-build] [--suites a,b,c] [--out DIR]
#
# 1. Compiled: `lake exe tests` (the natively compiled runner, Lean -> C -> clang).
# 2. Interpreted: `lake env lean scripts/interp-suites.lean`, whose #eval runs the same
#    registered suites (SafePdf.Tests.suites) in Lean's IR interpreter, loading the project
#    code from the .olean files instead of the compiled binary.
# 3. scripts/suite-diff.py compares the two outputs suite by suite, after replacing
#    wall-clock figures ("12.3 ms") by "<t>"; anything else that differs is a failure.
#
# A difference means the compiled code and the interpreted IR disagree: a Lean code
# generator (or C compiler) bug, or a test whose output depends on something other than its
# inputs (then fix the test). Neither run is trusted more than the other; both come from the
# same elaborated IR, so this probes codegen and the runtime, not the elaborator.
#
# --suites   comma-separated suite names (Tests/Main.lean), or `all`; default: the
#            deterministic subset DEFAULT_SUITES below. The compiled runner always runs every
#            suite (it has no selection); only the chosen suites' blocks are compared.
#            With `all`, suites that assert wall-clock bounds (TIMED_SUITES) are compared but
#            their differences are reported, not failures: the interpreter is far slower.
#            The `scaling` suite (task 13.3: wall-clock ratios t(2n)/t(n) of every public
#            entry point) is never run interpreted (SKIPPED_SUITES): its sizes are calibrated
#            to the compiled speed, so neither its numbers nor its verdict mean anything in
#            the interpreter, and it is left out of the comparison like a missing suite
#            (`--suites scaling` is refused). The compiled runner still runs it.
# --no-build skip `lake build tests` (CI runs it in an earlier step).
# --out DIR  keep compiled.out, interpreted.out and diff.txt in DIR (default: a temp dir,
#            removed at the end).
# Exit status: 0 when every compared suite agrees, 1 otherwise.
#
# Cost (measured 2026-11-23, Apple M-series, task 12.6): compiled run of every suite 112 s;
# interpreted, the 21 suites of DEFAULT_SUITES took 387 s in all (write-annots 177 s,
# write-incremental 112 s, write-confidentiality 68 s, the rest under 20 s each) and agreed
# with the compiled output; an interpreted run of every suite did not finish within 14 min
# (stopped; the raster *-spec property suites with thousands of cases each are the likely
# cost). `adversarial` asserts per-call time bounds and fails interpreted (xobject-fanout.pdf).
set -euo pipefail

DEFAULT_SUITES=smoke,golden,xref-views,streams-view,pages-view,crypt,svg-view,text-view,font-identity,cff-text,text-layout,text-unicode,write-incremental,write-annots,annot,open-settings,optional-content,attachments,write-confidentiality,raster-geom,raster-subst
TIMED_SUITES=adversarial
SKIPPED_SUITES=scaling


here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo="$(dirname "$here")"
cd "$repo"

build=1 suites="$DEFAULT_SUITES" outdir=""
while [ $# -gt 0 ]; do
  case "$1" in
    --no-build) build=0 ;;
    --suites) suites="${2:?--suites needs a comma-separated list}"; shift ;;
    --out) outdir="${2:?--out needs a directory}"; shift ;;
    -h|--help) sed -n '2,39p' "$0"; exit 0 ;;
    *) echo "usage: $0 [--no-build] [--suites a,b,c] [--out DIR]" >&2; exit 2 ;;
  esac
  shift
done
case "$suites" in *" "*) echo "compiled-vs-interpreted: --suites takes no spaces" >&2; exit 2 ;; esac
[ "$suites" = all ] && suites=""
for sk in ${SKIPPED_SUITES//,/ }; do
  case ",$suites," in
    *",$sk,"*) echo "compiled-vs-interpreted: suite '$sk' is excluded (wall-clock; see SKIPPED_SUITES)" >&2; exit 2 ;;
  esac
done
# The interpreted runner's selection: the chosen suites, or (for `all`) every registered
# suite except SKIPPED_SUITES.
interp_suites="$suites"
if [ -z "$interp_suites" ]; then
  interp_suites=$(grep -o '{ name := "[^"]*"' Tests/Main.lean | cut -d'"' -f2 \
    | grep -vxF -e "${SKIPPED_SUITES//,/$'\n'}" | paste -sd, -) || true
  [ -n "$interp_suites" ] || { echo "compiled-vs-interpreted: no suites found in Tests/Main.lean" >&2; exit 2; }
fi

if [ -z "$outdir" ]; then
  outdir="$(mktemp -d)"
  trap 'rm -rf "$outdir"' EXIT
else
  mkdir -p "$outdir"
  outdir="$(cd "$outdir" && pwd)"
fi

if [ "$build" = 1 ]; then lake build tests; fi

t0=$(date +%s)
# The compiled runner's exit status is its PASS/FAIL verdict; a failing suite must still be
# compared (the interpreter should fail the same way), so the status is reported, not fatal.
set +e
lake exe tests >"$outdir/compiled.out" 2>"$outdir/compiled.err"
crc=$?
set -e
t1=$(date +%s)
echo "compiled-vs-interpreted: compiled run exit $crc in $((t1 - t0)) s"

set +e
SAFEPDF_INTERP_OUT="$outdir/interpreted.out" SAFEPDF_SUITES="$interp_suites" \
  lake env lean scripts/interp-suites.lean >"$outdir/interpreted.err" 2>&1
irc=$?
set -e
t2=$(date +%s)
echo "compiled-vs-interpreted: interpreted run exit $irc in $((t2 - t1)) s"
if [ "$irc" != 0 ]; then
  echo "compiled-vs-interpreted: the interpreted runner failed:" >&2
  cat "$outdir/interpreted.err" >&2
  exit 1
fi
if grep -q '^\[MISSING\]' "$outdir/interpreted.out"; then
  grep '^\[MISSING\]' "$outdir/interpreted.out" >&2
  echo "compiled-vs-interpreted: unknown suite name(s) in --suites" >&2
  exit 1
fi

args=("$outdir/compiled.out" "$outdir/interpreted.out")
if [ -n "$suites" ]; then args+=(--suites "$suites"); else args+=(--ignore "$TIMED_SUITES"); fi
set +e
python3 -I "$here/suite-diff.py" "${args[@]}" | tee "$outdir/diff.txt"
drc=${PIPESTATUS[0]}
set -e
exit "$drc"
