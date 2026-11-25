import SafePdf
import SafePdf.Api
import SafePdf.Shell.Read
import SafePdf.Shell.Inspect
import SafePdf.Shell.App.Xfdf
import SafePdf.Shell.App.Save

/-!
# Capped reads and true strict mode (task 12.1)

Plan.md §6 Phase 12 "Capped reads + true strict mode", M12 "a growing input reads only
through the cap; a strict-only open records zero repair attempts"; `docs/safety.md` §5 0a.

* **Capped read** (`Shell.Read`): a counting stub reader over a source larger than the cap
  (`limitExceeded`, at most `cap + 1` bytes pulled); an endless source; a real file larger
  than the cap read through a counting handle; a real file that **grows while it is read**
  (each chunk read appends more to it, through another handle) — rejected after at most
  `cap + 1` bytes; a file growing but staying under the cap — accepted; exact-cap,
  cap + 1, empty; one-byte short reads; a reader returning more than asked.
* **Every read site**: `Api.openFile`, `Inspect.load`, `Xfdf.readFile`, `Save.diskStateAt`
  (the overwrite comparison) reject or flag a file above their cap.
* **True strict mode**: `parseLogged … false` on a file that needs repair → the strict error,
  `refused`, **zero repair attempts**; the same file with repair on opens repaired after one
  attempt; `Api.openBytes { allowRepair := false }` → `repairRefused`; a valid file opens
  strictly with zero attempts in both modes; a `/Prev` cycle stays a final error, not
  `refused`.
-/

namespace SafePdf.Tests.CappedRead

open SafePdf.Shell

/-- Reports a failed check; 1 on failure. -/
def check (what : String) (ok : Bool) : IO Nat := do
  if ok then return 0
  IO.println s!"  FAIL capped-read: {what}"
  return 1

/-- `true` iff `r` is `limitExceeded .inputBytes`. -/
def isCapErr {α : Type} : Except Error α → Bool
  | .error (.limitExceeded .inputBytes) => true
  | _ => false

/-- A stub reader over a virtual source of `total` bytes (`none`: endless), counting the
bytes it hands out in `pulled`; each call returns at most `n` and at most `maxChunk` bytes. -/
def stub (pulled : IO.Ref Nat) (total : Option Nat) (maxChunk : Nat := 1 <<< 20)
    (extra : Nat := 0) : USize → IO ByteArray := fun n => do
  let done ← pulled.get
  let left := match total with
    | some t => t - done
    | none => n.toNat + extra
  -- `extra`: a misbehaving reader returns more than asked.
  let k := min (min (n.toNat + extra) maxChunk) left
  pulled.set (done + k)
  return ⟨Array.replicate k 0x41⟩

/-- A minimal valid file with a correct xref table (`trailerExtra` added to the trailer,
`prevSelf`: `/Prev` is the table's own offset, a one-element cycle). -/
def validPdf (prevSelf : Bool := false) : ByteArray :=
  let body := "%PDF-1.4\n1 0 obj\n<< /Type /Catalog /Pages 2 0 R >>\nendobj\n" ++
    "2 0 obj\n<< /Type /Pages /Kids [] /Count 0 >>\nendobj\n"
  let x := body.utf8ByteSize
  let row (o : Nat) : String :=
    let s := toString o
    String.ofList (List.replicate (10 - s.length) '0') ++ s ++ " 00000 n \n"
  let prev := if prevSelf then s!" /Prev {x}" else ""
  (body ++ "xref\n0 3\n0000000000 65535 f \n" ++ row 9 ++ row 58 ++
    s!"trailer\n<< /Size 3 /Root 1 0 R{prev} >>\nstartxref\n{x}\n%%EOF\n").toUTF8

/-- A damaged file: objects and a trailer, no xref table (opens only by repair). -/
def damagedPdf : ByteArray :=
  ("%PDF-1.4\n1 0 obj\n<< /Type /Catalog /Pages 2 0 R >>\nendobj\n" ++
    "2 0 obj\n<< /Type /Pages /Kids [] /Count 0 >>\nendobj\ntrailer\n<< /Root 1 0 R >>\n%%EOF\n").toUTF8

/-- `n` bytes of `A`. -/
def filler (n : Nat) : ByteArray := ⟨Array.replicate n 0x41⟩

/-- The stub-reader checks. -/
def stubChecks : IO Nat := do
  let mut f := 0
  let cap := 3 * (1 <<< 20) + 5
  -- A source four times the cap: rejected, and only `cap + 1` bytes were pulled.
  let pulled ← IO.mkRef 0
  let r ← Read.readWith (stub pulled (some (4 * cap))) cap
  let n ← pulled.get
  f := f + (← check s!"large source: limitExceeded (pulled {n})" (isCapErr r && n == cap + 1))
  -- An endless (growing) source: still stops after `cap + 1` bytes.
  let pulled ← IO.mkRef 0
  let r ← Read.readWith (stub pulled none) cap
  let n ← pulled.get
  f := f + (← check s!"endless source: limitExceeded (pulled {n})" (isCapErr r && n == cap + 1))
  -- Exactly `cap` bytes: accepted whole; `cap + 1`: rejected.
  let pulled ← IO.mkRef 0
  let r ← Read.readWith (stub pulled (some cap)) cap
  f := f + (← check "exact cap: ok" (match r with | .ok b => b.size == cap | _ => false))
  let pulled ← IO.mkRef 0
  let r ← Read.readWith (stub pulled (some (cap + 1))) cap
  f := f + (← check "cap + 1: limitExceeded" (isCapErr r))
  -- Empty source; cap 0.
  let pulled ← IO.mkRef 0
  let r ← Read.readWith (stub pulled (some 0)) cap
  f := f + (← check "empty: ok" (match r with | .ok b => b.size == 0 | _ => false))
  let pulled ← IO.mkRef 0
  let r ← Read.readWith (stub pulled (some 1)) 0
  f := f + (← check "cap 0, one byte: limitExceeded" (isCapErr r))
  -- Short reads of one byte at a time: the fuel still reaches the end.
  let pulled ← IO.mkRef 0
  let r ← Read.readWith (stub pulled (some 1000) (maxChunk := 1)) 1000
  f := f + (← check "one-byte reads: ok" (match r with | .ok b => b.size == 1000 | _ => false))
  let pulled ← IO.mkRef 0
  let r ← Read.readWith (stub pulled none (maxChunk := 1)) 1000
  f := f + (← check "one-byte reads, endless: limitExceeded" (isCapErr r))
  -- A reader returning more than asked is truncated to the budget.
  let pulled ← IO.mkRef 0
  let r ← Read.readWith (stub pulled none (maxChunk := 1 <<< 22) (extra := 1 <<< 21)) cap
  f := f + (← check "oversized chunks: limitExceeded" (isCapErr r))
  return f

/-- The real-file checks, in the temporary directory `dir`. -/
def fileChecks (dir : System.FilePath) : IO Nat := do
  let mut f := 0
  let cap := 2 * (1 <<< 20) + 7
  -- A real file larger than the cap, read through a counting handle.
  let big := dir / "big.bin"
  IO.FS.writeBinFile big (filler (3 * cap))
  let pulled ← IO.mkRef 0
  let h ← IO.FS.Handle.mk big .read
  let r ← Read.readWith (fun n => do
    let c ← h.read n
    pulled.modify (· + c.size)
    return c) cap
  let n ← pulled.get
  f := f + (← check s!"big file via handle: limitExceeded (read {n} of {3 * cap})"
    (isCapErr r && n == cap + 1))
  -- `readFile` rejects it without reading (stat fast path).
  f := f + (← check "big file: readFile limitExceeded" (isCapErr (← Read.readFile big cap)))
  -- A file that grows while it is read: it starts below the cap; after every chunk read,
  -- another handle appends 1 MiB. The read stops after `cap + 1` bytes.
  let grow := dir / "grow.bin"
  IO.FS.writeBinFile grow (filler (1 <<< 20))
  let pulled ← IO.mkRef 0
  let appends ← IO.mkRef 0
  let h ← IO.FS.Handle.mk grow .read
  let w ← IO.FS.Handle.mk grow .append
  let r ← Read.readWith (fun n => do
    let c ← h.read n
    pulled.modify (· + c.size)
    w.write (filler (1 <<< 20))
    w.flush
    appends.modify (· + 1)
    return c) cap
  let n ← pulled.get
  let size := (← grow.metadata).byteSize.toNat
  f := f + (← check s!"growing file: limitExceeded after {n} bytes (file now {size})"
    (isCapErr r && n == cap + 1 && size > cap + 1))
  -- A file that grows but stays under the cap is accepted (read to its end at read time).
  let small := dir / "small.bin"
  IO.FS.writeBinFile small (filler 1000)
  let once ← IO.mkRef false
  let h ← IO.FS.Handle.mk small .read
  let w ← IO.FS.Handle.mk small .append
  let r ← Read.readWith (fun n => do
    let c ← h.read n
    unless ← once.get do
      w.write (filler 500); w.flush; once.set true
    return c) cap
  -- (The C stream's end-of-file flag is sticky, so the bytes appended after the first short
  -- read may or may not be seen; either way the result is a prefix within the cap.)
  f := f + (← check "growing under the cap: ok, 1000 or 1500 bytes"
    (match r with | .ok b => b.size == 1000 || b.size == 1500 | _ => false))
  -- Read sites.
  -- `Api.openFile`: a valid PDF over a small cap → limitExceeded; under it → opens.
  let pdf := dir / "valid.pdf"
  IO.FS.writeBinFile pdf (validPdf)
  match ← Api.openFile pdf { limits := { maxInputBytes := 100 } } with
  | .error (.pdf (.limitExceeded .inputBytes)) => pure ()
  | _ => f := f + (← check "Api.openFile over the cap: limitExceeded" false)
  match ← Api.openFile pdf with
  | .ok d => f := f + (← check "Api.openFile: not repaired" (!d.repaired))
  | .error e => f := f + (← check s!"Api.openFile: {e}" false)
  -- `Inspect.load` (the inspector's and the viewer's open).
  match ← Inspect.load { limits := { maxInputBytes := 100 } } pdf.toString with
  | .ok i => f := f + (← check "Inspect.load over the cap: limitExceeded, nothing kept"
      (isCapErr i.result && i.bytes.size == 0))
  | .error e => f := f + (← check s!"Inspect.load: {e}" false)
  match ← Inspect.load {} pdf.toString with
  | .ok i => f := f + (← check "Inspect.load: parses" (i.result matches .ok _))
  | .error e => f := f + (← check s!"Inspect.load: {e}" false)
  -- `Xfdf.readFile`: a file over `maxBytes` is refused as too large.
  let x := dir / "big.xfdf"
  IO.FS.writeBinFile x (filler 300)
  match ← App.Xfdf.readFile { maxBytes := 200 } x.toString with
  | .error msg => f := f + (← check s!"Xfdf.readFile too large: {msg}"
      (msg.startsWith "XFDF file too large"))
  | .ok _ => f := f + (← check "Xfdf.readFile over the cap" false)
  -- `Save.diskStateAt`: the overwrite comparison.
  let opened := validPdf
  let disk := dir / "disk.pdf"
  IO.FS.writeBinFile disk opened
  f := f + (← check "diskStateAt same" ((← App.Save.diskStateAt opened disk) == .same))
  let h ← IO.FS.Handle.mk disk .append
  h.write (filler (3 * (1 <<< 20))); h.flush
  f := f + (← check "diskStateAt grown: changed" ((← App.Save.diskStateAt opened disk) == .changed))
  IO.FS.writeBinFile disk (opened.extract 0 (opened.size - 1) |>.push 0x20)
  f := f + (← check "diskStateAt edited: changed" ((← App.Save.diskStateAt opened disk) == .changed))
  f := f + (← check "diskStateAt missing"
    ((← App.Save.diskStateAt opened (dir / "nonexistent.pdf")) == .missing))
  return f

/-- The strict-mode checks (pure). -/
def strictChecks : IO Nat := do
  let mut f := 0
  let lim := Limits.default
  -- A file that needs repair, strict only: the strict error, refused, zero repair attempts.
  match parseLogged lim damagedPdf false with
  | (.error e, log) =>
    f := f + (← check s!"damaged, strict only: refused with 0 attempts ({reprStr e})"
      (log.attempts == 0 && log.refused && !e.isFinal))
  | (.ok _, _) => f := f + (← check "damaged, strict only: must fail" false)
  -- The same file with repair on: one attempt, repaired.
  match parseLogged lim damagedPdf true with
  | (.ok d, log) => f := f + (← check "damaged, repair on: 1 attempt, repaired"
      (log.attempts == 1 && !log.refused && d.repaired))
  | (.error e, _) => f := f + (← check s!"damaged, repair on: {reprStr e}" false)
  -- `parseWith` (default repair on) is unchanged.
  f := f + (← check "parseWith repairs by default"
    (match parseWith lim damagedPdf with | .ok d => d.repaired | _ => false))
  -- The API: strict mode → repairRefused carrying the strict error.
  match Api.openBytes damagedPdf { allowRepair := false } with
  | .error (.repairRefused _) => pure ()
  | _ => f := f + (← check "Api strict: repairRefused" false)
  -- A large damaged file whose repair scan is expensive (many unterminated strings):
  -- strict only does no repair work.
  let junk := String.join (List.replicate 20000 "1 0 obj (")
  let slow := damagedPdf ++ junk.toUTF8
  let t0 ← IO.monoNanosNow
  let (r, log) ← IO.lazyPure fun _ => parseLogged lim slow false
  let t1 ← IO.monoNanosNow
  f := f + (← check s!"slow damaged, strict only: 0 attempts ({(t1 - t0) / 1000000} ms)"
    (log.attempts == 0 && log.refused && r matches .error _))
  -- A valid file: strict in both modes, zero attempts.
  for ar in [true, false] do
    match parseLogged lim validPdf ar with
    | (.ok d, log) => f := f + (← check s!"valid (allowRepair {ar}): strict, 0 attempts"
        (log.attempts == 0 && !log.refused && !d.repaired))
    | (.error e, _) => f := f + (← check s!"valid (allowRepair {ar}): {reprStr e}" false)
  -- A `/Prev` cycle is final in both modes: not refused, no repair.
  for ar in [true, false] do
    match parseLogged lim (validPdf (prevSelf := true)) ar with
    | (.error e, log) => f := f + (← check s!"prev cycle (allowRepair {ar}): final, 0 attempts"
        (e.isCycle && log.attempts == 0 && !log.refused))
    | (.ok _, _) => f := f + (← check s!"prev cycle (allowRepair {ar}): must fail" false)
  match Api.openBytes (validPdf (prevSelf := true)) { allowRepair := false } with
  | .error (.pdf (.cycle _ _)) => pure ()
  | _ => f := f + (← check "Api strict, prev cycle: pdf cycle error" false)
  return f

/-- Runs the suite; returns the number of failures. -/
def run : IO Nat := do
  let dir ← IO.FS.createTempDir
  try
    return (← stubChecks) + (← fileChecks dir) + (← strictChecks)
  finally
    try IO.FS.removeDirAll dir catch _ => pure ()

end SafePdf.Tests.CappedRead
