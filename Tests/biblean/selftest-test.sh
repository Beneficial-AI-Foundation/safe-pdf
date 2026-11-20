#!/usr/bin/env bash
# `viewer --biblean --self-test` against our stub server (task 10.4; Plan.md §6 Phase 10
# "Conformance"). Run from anywhere:
#   Tests/biblean/selftest-test.sh [--no-build]
#
# The stub mode of scripts/biblean-contract.sh: the viewer-side checks of bib-lean's
# reader-contract script (S2–S5, S7–S9, S11, S12, S23, S24, adapted to the self-test's
# payload) plus X1–X7 (the PUT file, exit codes 1/2/3, token hygiene), with
# Tests/biblean/stub_server.py; the bib-lean-side checks are skipped. No display, no bib-lean
# checkout. For the full S1–S25 against a real bib-lean server:
#   scripts/biblean-contract.sh --biblean /path/to/biblean
# Exit 0 on success.
set -u
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
exec "$here/../../scripts/biblean-contract.sh" --stub "$@"
