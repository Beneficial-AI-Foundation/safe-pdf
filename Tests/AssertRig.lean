/-!
# Assertions-build rig (task 13.10; Plan.md §6 Phase 13, §4 S1/S3)

Self-test of `scripts/asserts.sh`. The assertions build compiles the generated C without
`NDEBUG`, so `assert(i < lean_array_size(o))` in `lean.h`'s `lean_array_get_core` and its
siblings (`lean_array_fget`, `lean_byte_array_uget`, ...) is live: that check sits behind every
proof-carrying index `a[i]'h`, whose proof the compiler erases. This executable performs such
a read with a **forged** proof, deliberately out of range. Under the assertions build it must
abort (`lean_notify_assert` prints `LEAN ASSERTION VIOLATION` and aborts: exit status 134,
SIGABRT); under the release build (`-DNDEBUG`) the same read returns whatever lies past the
array, so a rig that "passes" there proves nothing. `scripts/asserts.sh` runs it as an
expected-failure subprocess and fails when it does not abort.

Usage: `assert-rig MODE`, `MODE` one of
* `control` : an in-range proof-carrying read of an `Array` and of a `ByteArray` with proofs
  that are checked; prints `control ok` and exits 0 (the rig itself is sound: it does not
  abort for another reason);
* `array` : out-of-range proof-carrying read of an `Array Nat` (`lean_array_fget`);
* `bytes` : out-of-range proof-carrying read of a `ByteArray` (`lean_byte_array_uget`).

This module is test-only and unverified (outside the strict modules): it uses `unsafe` to
forge a proof, which the hygiene guard allows only here. It is not part of the umbrella and
not linked into any shipped executable (`lean_exe «assert-rig»` is not a default target).
-/

namespace SafePdf.Tests.AssertRig

set_option linter.defProp false in
/-- A forged proof that `i < n`. Proofs are erased by the compiler, so nothing is checked at
run time except the `assert` inside `lean.h`'s accessors. -/
unsafe def forge (i n : Nat) : i < n := unsafeCast ()

/-- Read `a[i]` with a forged bound proof. `noinline` so the compiler cannot see the index and
the array size together. -/
@[noinline] unsafe def readArray (a : Array Nat) (i : Nat) : Nat :=
  a[i]'(forge i a.size)

/-- Read `bs[i]` with a forged bound proof (same reason for `noinline`). -/
@[noinline] unsafe def readBytes (bs : ByteArray) (i : Nat) : UInt8 :=
  bs[i]'(forge i bs.size)

/-- In-range reads with genuine proofs: the rig's baseline. The sizes and indices come from
the argument list so that nothing is constant-folded. -/
@[noinline] def control (n : Nat) : IO UInt32 := do
  let a := (Array.range (n + 4))
  let bs := ByteArray.mk (a.map (·.toUInt8))
  let mut sum := 0
  for h : i in [0:a.size] do
    sum := sum + a[i]'(Membership.get_elem_helper h rfl)
  for h : i in [0:bs.size] do
    sum := sum + (bs[i]'(Membership.get_elem_helper h rfl)).toNat
  IO.println s!"control ok ({sum})"
  return 0

/-- Entry point (see the module doc). -/
unsafe def run (args : List String) : IO UInt32 := do
  -- The array has `4 + extra` elements and the read index is `4 + extra + 1`, one past the end;
  -- `extra` comes from the environment-free argument list so it is unknown at compile time.
  let extra := args.length
  match args with
  | "control" :: _ => control extra
  | "array" :: _ =>
    let a := Array.range (4 + extra)
    IO.println s!"array: reading index {a.size + 1} of {a.size}"
    (← IO.getStdout).flush
    IO.println s!"array: read {readArray a (a.size + 1)} (no assertion fired)"
    return 0
  | "bytes" :: _ =>
    let bs := ByteArray.mk ((Array.range (4 + extra)).map (·.toUInt8))
    IO.println s!"bytes: reading index {bs.size + 1} of {bs.size}"
    (← IO.getStdout).flush
    IO.println s!"bytes: read {readBytes bs (bs.size + 1)} (no assertion fired)"
    return 0
  | _ =>
    IO.eprintln "usage: assert-rig control|array|bytes"
    return 2

end SafePdf.Tests.AssertRig

/-- Executable entry point. -/
unsafe def main (args : List String) : IO UInt32 := SafePdf.Tests.AssertRig.run args
