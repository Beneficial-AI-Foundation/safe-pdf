#!/usr/bin/env bash
# Proof-hygiene guard (Plan.md section 3 rule 3, tasks 0.3 and 13.9). Run from the repo root.
#   scripts/check-hygiene.sh [--root DIR] [--lib DIR] [--no-axioms] [--no-envscan] [--no-source]
# --root DIR     scan DIR's sources (and the strict modules found there) instead of the current
#                directory (for testing the guard itself, scripts/test-hygiene.sh)
# --lib DIR      extra directory with built .oleans of the modules under --root (the self-test)
# --no-axioms    skip the `#print axioms` check (it needs built .oleans)
# --no-envscan   skip the environment scan (scripts/envscan.lean; it needs built .oleans)
# --no-source    skip the source scan
# Steps: source scan (hygiene.py), `#print axioms` (axioms.lean), environment scan (envscan.lean).
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo="$(dirname "$here")"
root="."
lib=""
axioms=1
envscan=1
source=1
while [ $# -gt 0 ]; do
  case "$1" in
    --root) root="${2:?--root needs a directory}"; shift 2 ;;
    --lib) lib="${2:?--lib needs a directory}"; shift 2 ;;
    --no-axioms) axioms=0; shift ;;
    --no-envscan) envscan=0; shift ;;
    --no-source) source=0; shift ;;
    *) echo "usage: $0 [--root DIR] [--lib DIR] [--no-axioms] [--no-envscan] [--no-source]" >&2; exit 2 ;;
  esac
done

status=0
if [ "$source" = 1 ]; then
  python3 -I "$here/hygiene.py" scan --root "$root" || status=1
fi

if [ "$axioms" = 1 ]; then
  (
    cd "$repo"
    if out="$(lake env lean scripts/axioms.lean 2>&1)"; then
      printf '%s\n' "$out" | python3 -I "$here/hygiene.py" axioms
    else
      printf '%s\n' "$out" >&2
      echo "axioms: scripts/axioms.lean failed to elaborate" >&2
      exit 1
    fi
  ) || status=1
fi

if [ "$envscan" = 1 ]; then
  # --root is made absolute before the cd into the repo (lake env needs the repo's lakefile)
  absroot="$(cd "$root" && pwd)"
  mods="$(python3 -I "$here/hygiene.py" modules --root "$absroot")"
  if [ -z "$mods" ]; then
    echo "envscan: no strict modules under $root" >&2
    status=1
  else
    (
      cd "$repo"
      if [ -n "$lib" ]; then export ENVSCAN_LIB="$(cd "$lib" && pwd)"; fi
      # shellcheck disable=SC2086  # one argument per module name
      lake env lean --run scripts/envscan.lean $mods
    ) || status=1
  fi
fi
exit $status
