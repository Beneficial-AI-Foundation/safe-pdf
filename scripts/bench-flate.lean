import SafePdf.Core.Filter.Flate

/-!
# Flate throughput benchmark (task 3.11; Plan.md §8 "Inflate performance in Lean (M3)")

Decodes each zlib file given on the command line with `Flate.flateDecode` (limit 1 GiB,
Adler-32 checked) and prints the output size, the best wall time of `--reps` runs (default 3)
and the throughput in MiB/s of output.

Run it compiled, not interpreted (the interpreter is ~100× slower):

    scripts/bench-flate.sh file1.z file2.z …

`bench-flate.sh` builds the library, compiles this file with `lean -c` and links it against the
library's object files with `leanc`, so no lakefile target is needed. Inputs can be made with
Python's `zlib` (`zlib.compress(data, 6)`).
-/

open SafePdf SafePdf.Core.Filter

/-- Run the decoder between two clock readings; the result is matched on before the second
reading so the work cannot float past it. Returns the output size (or `none`) and ns. -/
@[noinline] def timeOnce (input : ByteArray) : IO (Option Nat × Nat) := do
  let t0 ← IO.monoNanosNow
  match Flate.flateDecode { Limits.default with maxDecodedStreamBytes := 1 <<< 30 } input with
  | .ok out => do
    let t1 ← IO.monoNanosNow
    pure (some out.size, t1 - t0)
  | .error _ => do
    let t1 ← IO.monoNanosNow
    pure (none, t1 - t0)

/-- Best of `reps` runs. -/
def bench (reps : Nat) (input : ByteArray) : IO (Option Nat × Nat) := do
  let mut best : Option Nat × Nat := (none, 0)
  for i in [0:reps] do
    let r ← timeOnce input
    if i == 0 || r.2 < best.2 then best := r
  pure best

/-- Entry point: `[--reps N] file…`. -/
def main (args : List String) : IO UInt32 := do
  let (reps, files) := match args with
    | "--reps" :: n :: rest => (n.toNat?.getD 3, rest)
    | rest => (3, rest)
  for f in files do
    let input ← IO.FS.readBinFile f
    let (r, ns) ← bench reps input
    match r with
    | none => IO.println s!"{f}: decode FAILED"
    | some n =>
      let mibs := (n.toFloat / 1048576.0) / (ns.toFloat / 1.0e9)
      IO.println s!"{f}: in {input.size} B, out {n} B, {ns / 1000000} ms, {mibs} MiB/s"
  pure 0
