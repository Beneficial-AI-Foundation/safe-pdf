import SafePdf.Shell.Fonts
import SafePdf.Shell.Worker.Protocol

/-!
# Document worker: frame I/O shared by the worker and the client (task 12.2a)

Plan.md §6 Phase 12 ("Restricted, stoppable document worker"). Unverified shell code (`IO`):
reading and writing the frames of `SafePdf.Shell.Worker.Protocol` on a byte stream. Reading
is exactly `Protocol.decodeFrame` split into its two steps — the 4-byte header
(`Protocol.readHeader`, checked against the cap **before** any payload byte is read, so an
over-long header costs nothing) and then the payload (`Protocol.decodeBody`).

`workerFonts` is the substitute-font table the worker renders with. It searches only the
fixed system font directories (`Shell.Fonts.findFacesIn` with an empty `SearchConfig`: no
`$HOME`, no `$SAFEPDF_FONT_DIR`), so it does not depend on the environment, which the client
clears (`inheritEnv := false`). Tests render in-process with the same table to compare pixels.
-/

namespace SafePdf.Shell.Worker

open SafePdf SafePdf.Core

/-- Read exactly `n` bytes from `s`, in chunks of at most 1 MiB; fewer only at end of input.
The buffer grows with the data actually received (no up-front allocation of `n` bytes). -/
def readExact (s : IO.FS.Stream) (n : Nat) : IO ByteArray := do
  let mut buf := ByteArray.emptyWithCapacity (min n (1 <<< 20))
  while buf.size < n do
    let chunk ← s.read (min (n - buf.size) (1 <<< 20)).toUSize
    if chunk.isEmpty then break
    buf := buf ++ chunk
  return buf

/-- What arrives on a stream. -/
inductive Incoming where
  /-- End of input before a frame started. -/
  | eof
  /-- A complete frame's payload. -/
  | frame (payload : ByteArray)
  /-- A header announcing `len` bytes, above the cap (the payload was not read). -/
  | tooLong (len : Nat)
  /-- End of input inside a frame (`got` bytes of the frame received). -/
  | truncated (got : Nat)

/-- Read one frame with payload cap `cap`. -/
def readFrame (s : IO.FS.Stream) (cap : Nat) : IO Incoming := do
  let hdr ← readExact s 4
  if hdr.size == 0 then return .eof
  match Protocol.readHeader hdr 0 with
  | none => return .truncated hdr.size
  | some len =>
    if cap < len then return .tooLong len
    let body ← readExact s len
    if body.size < len then return .truncated (4 + body.size)
    return .frame body

/-- Write bytes and flush. -/
def writeAll (s : IO.FS.Stream) (b : ByteArray) : IO Unit := do
  s.write b
  s.flush

/-- **The worker's substitute fonts**: the standard-14 substitutes found in the fixed system
font directories only (no `$HOME`, no `$SAFEPDF_FONT_DIR`; environment-independent). -/
def workerFonts (limits : Limits) : IO Raster.Subst.SubstFonts := do
  let cfg ← Fonts.listVersions {}
  return Fonts.tableOf limits (← Fonts.findFacesIn cfg)

/-- `Core.Doc.Rotation` as quarter turns. -/
def rotationToNat : Doc.Rotation → Nat
  | .r0 => 0
  | .r90 => 1
  | .r180 => 2
  | .r270 => 3

/-- Quarter turns as a `Core.Doc.Rotation` (`none` above 3). -/
def rotationOfNat? : Nat → Option Doc.Rotation
  | 0 => some .r0
  | 1 => some .r90
  | 2 => some .r180
  | 3 => some .r270
  | _ => none

end SafePdf.Shell.Worker
