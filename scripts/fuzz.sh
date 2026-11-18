#!/usr/bin/env bash
# Fuzz smoke campaign (Plan.md §6 Phase 0): build the `fuzz` executable and run a short,
# deterministic campaign against the parser entry points (`SafePdf.parse`, `parseObjectAt`,
# `parseIndirectAt`, `Core.Lex.lexAll`). Extra arguments are passed to the fuzzer
# and override the defaults below (later flags win), e.g. `scripts/fuzz.sh --iters 100000`.
# Seed directories Tests/adversarial and corpus are used when present.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build fuzz
exec lake exe fuzz --iters 2000 --seed 20260101 --max-len 4096 "$@"
