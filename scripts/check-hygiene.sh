#!/usr/bin/env bash
# Proof-hygiene guard (Plan.md section 3 rule 3, task 0.3). Run from the repo root.
#   scripts/check-hygiene.sh [--root DIR] [--no-axioms]
# --root DIR  scan DIR instead of the current directory (for testing the guard itself)
# --no-axioms skip the `#print axioms` check (it needs built .oleans in the main checkout)
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo="$(dirname "$here")"
root="."
axioms=1
while [ $# -gt 0 ]; do
  case "$1" in
    --root) root="${2:?--root needs a directory}"; shift 2 ;;
    --no-axioms) axioms=0; shift ;;
    *) echo "usage: $0 [--root DIR] [--no-axioms]" >&2; exit 2 ;;
  esac
done

status=0
python3 -I "$here/hygiene.py" scan --root "$root" || status=1

if [ "$axioms" = 1 ]; then
  cd "$repo"
  if out="$(lake env lean scripts/axioms.lean 2>&1)"; then
    printf '%s\n' "$out" | python3 -I "$here/hygiene.py" axioms || status=1
  else
    printf '%s\n' "$out" >&2
    echo "axioms: scripts/axioms.lean failed to elaborate" >&2
    status=1
  fi
fi
exit $status
