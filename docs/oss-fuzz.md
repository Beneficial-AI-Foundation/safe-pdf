# OSS-Fuzz onboarding plan

Task 12.6 (Plan.md §6 Phase 12, "Independent verification"; `docs/safety.md` §5 item 10).
Status: **plan only.** Nothing here has been submitted to OSS-Fuzz or run under libFuzzer;
the blockers below have to be cleared first.

## Why fuzz a verified core at all

The core's theorems say every entry point is total and bounded (S1–S3), so a fuzzer cannot
find a crash *in the proofs' model*. What it can find lies outside that model:

* **Codegen and runtime**: the Lean → C compiler, `lean.h` inlines, the runtime's allocator
  and reference counting, `ByteArray`/`Array` bounds checks on the compiled path, stack
  depth of non-tail recursion on hostile nesting (the proofs bound *fuel*, not native stack).
* **Resource behaviour**: inputs that stay within `Limits` but are slow or memory-hungry in
  compiled code (the timeout and RSS limits of ClusterFuzz report these).
* **The C shim**: `macos/safepdf_core.c` (task 11.1) marshals pointers, sizes and strings by
  hand; that code has no proofs at all.
* **Spec misreadings are out of scope** for a fuzzer: it checks robustness, not that we
  parse what Acrobat parses (that is the differential suites' job).

The in-tree campaign (`Tests/Fuzz/Main.lean`, `scripts/fuzz.sh`) already drives the parser
entry points deterministically in CI; OSS-Fuzz adds coverage guidance, scale (continuous,
many cores), sanitizers on the C side, and triage.

## What to fuzz

All targets take one byte buffer, so libFuzzer's `LLVMFuzzerTestOneInput(data, size)` maps
onto them directly. In order of value:

| Target | Entry point | Notes |
|---|---|---|
| `fuzz_open` | `SafePdf.Api.openBytes` (strict, then with repair) | xref, object streams, encryption dictionaries, repair scan |
| `fuzz_render` | `openBytes` + `Api.renderPage` on page 0 at zoom 1/4 | content streams, fonts, images, shading; the slowest, largest surface |
| `fuzz_text` | `openBytes` + `Api.pageText` on the first pages | text layout, ToUnicode / CMap chains |
| `fuzz_lex` | `Core.Lex.lexAll`, `parseObjectAt` | cheap, high exec/s; finds runtime issues fast |
| `fuzz_filters` | the `SafePdf/Core/Filter/` decoders (Flate, LZW, ASCII hex/85, RunLength, predictors) and the `Quarantine/` image decoders (CCITT, DCT) on raw bytes, with a 1-byte selector prefix | structure-free, very high exec/s |
| `fuzz_xfdf` | the XFDF parser (`SafePdf.Shell.App.Xfdf.parse`) | the only non-PDF input format |
| `fuzz_capi` | `safepdf_open_bytes` + `safepdf_render` through `macos/safepdf_core.h` | exercises the hand-written C marshalling under ASan/UBSan |

Seeds: `Tests/adversarial/*.pdf`, `Tests/golden/**/*.pdf`, the generated fixtures under
`Tests/fixtures-*`, and (not redistributed; fetched by the build script from the manifest,
hash-verified) a few small files of the pinned corpus subset (`scripts/corpus/pinned.txt`).
A PDF dictionary (`/Type`, `/Filter`, `obj`, `endobj`, `stream`, `xref`, `trailer`, `startxref`,
operators `BT ET Tf Tj TJ cm re f S Do`, …) as `fuzz_*.dict` helps libFuzzer a lot.

## Harness shape

Two ways to get a libFuzzer binary; plan for (A), keep (B) as the fallback.

**(A) Lean `@[export]` + a C harness (preferred).** A new module `SafePdf/Shell/FuzzEntry.lean`
exports one function per target, e.g.

```lean
@[export safepdf_fuzz_open] def fuzzOpen (b : ByteArray) : UInt32 := …  -- 0 = ran, result discarded
```

and `fuzz/fuzz_open.c` initialises the runtime once (as `safepdf_init` does: `lean_initialize_runtime_module`,
the module initialiser of the closure, `lean_io_mark_end_initialization`), then per input
copies `data` into a `lean_alloc_sarray`, calls the export and `lean_dec`s the result.
The Lake side mirrors `target macosFfi` (task 11.1): a static library of the
`FuzzEntry` closure, linked by the OSS-Fuzz build with `$LIB_FUZZING_ENGINE`.

`fuzz_capi` needs a bytes-based open in the C API, which does not exist yet:
`safepdf_open` takes a path. Add `safepdf_open_bytes(const uint8_t *data, size_t len,
char **error)` over `Api.openBytes` (a small change to `SafePdf/Shell/Ffi.lean` and
`macos/safepdf_core.{h,c}`; useful for embedders anyway). Until then, `fuzz_capi` writes the
input to a temp file, which works but is slower.

**(B) Pure-Lean driver.** Keep `Tests/Fuzz/Main.lean` and run it under OSS-Fuzz as a
"blackbox" fuzzer. No coverage guidance; only worth it if (A) stalls.

## Build script outline (`projects/safe-pdf/build.sh`)

```bash
#!/bin/bash -eu
# Toolchain: elan pinned by commit (same as .github/workflows/ci.yml), then lean-toolchain.
curl -sSfL "https://raw.githubusercontent.com/leanprover/elan/$ELAN_REF/elan-init.sh" -o /tmp/elan-init.sh
echo "$ELAN_INIT_SHA256  /tmp/elan-init.sh" | sha256sum -c -
sh /tmp/elan-init.sh -y --default-toolchain none
export PATH="$HOME/.elan/bin:$PATH"
cd "$SRC/safe-pdf"
elan toolchain install "$(cat lean-toolchain)"

# Lean -> C for the fuzz entry closure (lake's own clang compiles Lean's C output).
lake build fuzzEntry                      # -> .lake/build/lib/libsafepdffuzz.a
prefix="$(lean --print-prefix)"

# The harnesses with OSS-Fuzz's compiler and flags (sanitizers, coverage).
for t in open render text lex filters xfdf; do
  $CC $CFLAGS -I "$prefix/include" -c "fuzz/fuzz_$t.c" -o "$WORK/fuzz_$t.o"
  $CXX $CXXFLAGS "$WORK/fuzz_$t.o" .lake/build/lib/libsafepdffuzz.a \
    -L "$prefix/lib/lean" -lInit -lStd -lleanrt -lleancpp -lgmp -luv -lpthread -ldl \
    $LIB_FUZZING_ENGINE -o "$OUT/fuzz_$t"
  zip -j "$OUT/fuzz_${t}_seed_corpus.zip" Tests/adversarial/*.pdf
  cp fuzz/pdf.dict "$OUT/fuzz_$t.dict"
done
```

The Dockerfile starts `FROM gcr.io/oss-fuzz-base/base-builder`, `git clone`s the repo and
installs `curl`, `zip`. No network access at fuzz time.

## `project.yaml` draft

```yaml
homepage: "https://github.com/Beneficial-AI-Foundation/safe-pdf"
language: c          # the harnesses; the Lean code arrives as generated C
primary_contact: "<maintainer e-mail, to be chosen by the maintainers>"
main_repo: "https://github.com/Beneficial-AI-Foundation/safe-pdf"
fuzzing_engines:
  - libfuzzer
  - afl
sanitizers:
  - address
  - undefined
  # memory: needs every linked library MSan-instrumented, incl. libleanrt / libgmp / libuv;
  # leave out until the Lean runtime is rebuilt with -fsanitize=memory (blocker 3).
architectures:
  - x86_64
```

OSS-Fuzz accepts projects with a significant user base or critical role; a pre-release
viewer may be declined. The same harnesses then run under **ClusterFuzzLite** in our own CI
(GitHub Action `google/clusterfuzzlite`, same `build.sh` / Dockerfile), which needs no
acceptance and is the realistic first step.

## Blockers and open questions

1. **Lean runtime in the base-builder image.** Lean's release tarball ships its own `clang`
   and links Lean code against bundled `libc++`/glibc stubs (see `lakefile.lean` on Linux
   sysroots). The harness must instead be linked by OSS-Fuzz's clang with
   `$LIB_FUZZING_ENGINE`. Untested: whether `libleanrt.a`, `libInit.a`, `libStd.a` from the
   release link cleanly with the base image's clang/libc++, or whether Lean has to be built
   from source inside the image (slow: ~30 min, but cacheable).
2. **Coverage instrumentation of Lean code.** `lake` compiles the generated C with its own
   clang and flags; for coverage guidance the generated C (`.lake/build/ir/**/*.c`) must be
   compiled with `$CC $CFLAGS` (which carry `-fsanitize=fuzzer-no-link` and the sanitizer).
   Plan: take the `.c` files from `.lake/build/ir` after `lake build`, compile them in
   `build.sh` ourselves. Without that, libFuzzer only sees the harness, i.e. blackbox.
3. **Sanitizers.** ASan/UBSan should work on generated C plus a rebuilt runtime; with the
   prebuilt `libleanrt.a` only the harness and our objects are instrumented. MSan needs the
   whole runtime and `gmp`/`uv` instrumented: out of scope at first.
4. **Runtime initialisation cost.** Module initialisers of the whole closure run once per
   process (they build `Limits`, font tables, CMaps…); measure it. Fork mode / persistent
   mode keep it out of the per-input cost.
5. **Lean panics and `IO` errors.** The core has no `panic!`, but the runtime aborts on
   out-of-memory and on stack overflow; ClusterFuzz will (correctly) report those. Decide
   per class whether it is a bug (unbounded native recursion: yes) or an accepted limit.
6. **Timeouts vs `Limits`.** ClusterFuzz's default 25 s per input is far above our budgets,
   but `fuzz_render` at default limits can legitimately take seconds; pass a reduced
   `Limits` record in the fuzz entries (smaller decode budget, page size cap) so slow-unit
   reports mean real problems.
7. **Threading.** The C API requires `safepdf_thread_enter` off the main thread; libFuzzer
   calls the harness on the main thread, so no change is needed, but `-fork=N` / AFL
   persistent mode must be checked once.

## Steps

1. Add `safepdf_open_bytes` to the C API and `SafePdf/Shell/FuzzEntry.lean` with one export
   per target; a `fuzzEntry` Lake target modelled on `macosFfi`.
2. Write `fuzz/fuzz_*.c` and `fuzz/pdf.dict`; run them locally with clang `-fsanitize=fuzzer,address`.
3. ClusterFuzzLite in CI (a short PR-time run plus a nightly batch), via a `.clusterfuzzlite/`
   directory with the Dockerfile and `build.sh` above. (CI workflow changes go through a patch
   under `docs/`, since pushes cannot touch `.github/workflows/`.)
4. Once stable, file the OSS-Fuzz project (`projects/safe-pdf/` with `project.yaml`,
   `Dockerfile`, `build.sh`).
