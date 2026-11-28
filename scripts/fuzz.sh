#!/usr/bin/env bash
# Fuzz campaigns (Plan.md §6 Phase 0 and Phase 13): build the `fuzz` executable and run a
# deterministic campaign against the parser entry points (`SafePdf.parse`, `parseObjectAt`,
# `parseIndirectAt`, `Core.Lex.lexAll`) and the content-stream interpreter
# (`Core.Content.runBytes`).
#
# Usage: scripts/fuzz.sh [smoke|long] [fuzzer arguments...]
#   smoke  (default) 2,000 short inputs (max 4096 bytes, seed files whole): the CI smoke step.
#   long   task 13.6: the repetition mutator (a token, operator, dictionary entry, object or
#          seed slice repeated 10^3 .. 9*10^6 times, inputs up to 4 MiB), every call held to a
#          linear budget, bounded run time: 240 s (`FUZZ_LONG_SECONDS` overrides), after which
#          no new iteration starts (the last one may take up to a minute). A call over its
#          budget prints `fuzz: FAIL ...` and the exit code is 3.
# Extra arguments are passed to the fuzzer and override the profile's defaults (later flags
# win), e.g. `scripts/fuzz.sh --iters 100000` or `scripts/fuzz.sh long --seed 7`. Seed
# directories Tests/adversarial and corpus are used when present.
set -euo pipefail
cd "$(dirname "$0")/.."
profile=smoke
case "${1:-}" in
  smoke|long) profile=$1; shift ;;
esac
lake build fuzz
case "$profile" in
  smoke) exec lake exe fuzz --iters 2000 --seed 20260101 --max-len 4096 "$@" ;;
  long)  exec lake exe fuzz --long --iters 100000 --seed 20260128 --max-len 4096 \
           --time-limit "${FUZZ_LONG_SECONDS:-240}" "$@" ;;
esac
