import SafePdf.Shell.Fonts
import SafePdf.Shell.Worker.Protocol

/-!
# Document worker: frame I/O shared by the worker and the client (task 12.2a)

Plan.md §6 Phase 12 ("Restricted, stoppable document worker"). Unverified shell code (`IO`):
reading and writing the frames of `SafePdf.Shell.Worker.Protocol` on a byte stream. Reading
is exactly `Protocol.decodeFrame` split into its two steps — the 4-byte header
(`Protocol.readHeader`, checked against the cap **before** any payload byte is read, so an
over-long header costs nothing) and then the payload (`Protocol.decodeBody`).

`workerFonts` is the substitute-font table the worker renders with. It searches the fixed
system font directories plus what the startup configuration names (task 12.2d: flags
`--home=DIR` for `DIR/Library/Fonts`, `--font-dir=DIR`, `--no-subst`; the viewer passes its
`$HOME`, `$SAFEPDF_FONT_DIR` and `$SAFEPDF_SUBST_FONTS=0` this way), so it does not depend on
the environment, which the client clears (`inheritEnv := false`). The worker reads these files
once at startup, before it confines itself (task 12.2b). Tests render in-process with the same
table to compare pixels.
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

/-- The substitute faces the worker uses (file, bytes, face index): none with `noSubst`,
else those found in the fixed system font directories and in the directories the startup
configuration names (`home`'s `Library/Fonts`, `fontDirs`) — the viewer's own search
(`Fonts.systemConfig`) when the viewer passes its environment as flags (task 12.2d). Every
file is read here, in full; the worker calls this once, **before** it confines itself (task
12.2b, `SafePdf.Shell.Worker.Sandbox.prepare`), and opens no file afterwards. -/
def workerFaces (c : Protocol.StartConfig := {}) : IO (List Fonts.Found) := do
  if c.noSubst then return []
  let cfg ← Fonts.listVersions
    { home := c.home.map System.FilePath.mk, userDirs := c.fontDirs }
  Fonts.findFacesIn cfg

/-- **The worker's substitute fonts**: the table of `workerFaces c` (parsed lazily, purely,
under `limits`). Tests render in-process with the same table. -/
def workerFonts (limits : Limits) (c : Protocol.StartConfig := {}) :
    IO Raster.Subst.SubstFonts := do
  return Fonts.tableOf limits (← workerFaces c)

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
