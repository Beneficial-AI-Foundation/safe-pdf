import SafePdf.Core.Error

/-!
# Capped file reads (task 12.1; Plan.md §6 Phase 12 "Capped reads + true strict mode",
`docs/safety.md` §5 item 0a)

Every whole-file read of untrusted input goes through `readFile`: the PDF opens
(`Api.openFile`, the inspector's and the viewer's `Inspect.load`), XFDF import
(`Xfdf.readFile`), the overwrite comparison before Save (`Save.readDisk`) and the read-back
of Save's temporary file.

The read never trusts the file's size from `stat`: it reads **through a handle with a byte
budget** of `cap + 1` bytes, in chunks of at most `chunkBytes`, and stops at end of file. A
file that grows while it is read (or between a `stat` and the read) therefore allocates at
most `cap + 1` bytes before it is rejected with `Error.limitExceeded kind`. The `stat` that
`readFile` makes first is only a fast path: a file already larger than `cap` is rejected
without reading a byte.

`readWith` is the loop over an arbitrary chunk reader, so tests can drive it with a stub
(a counting or endlessly growing source) and assert on the bytes it pulled.

Shell code: `IO` allowed; no `partial` (the loop is structural on an explicit fuel that a
counting argument shows is never exhausted: every non-empty chunk adds at least one byte and
the loop stops at `cap + 1` bytes).
-/

namespace SafePdf.Shell.Read

/-- The largest chunk one `read` call asks for: 1 MiB. -/
def chunkBytes : Nat := 1 <<< 20

/-- The read loop: at most `fuel` calls of `read`, accumulating into `acc`, never asking for
more than `cap + 1 - acc.size` bytes. Returns the bytes read; `acc.size ≤ cap + 1` is kept
as long as `read n` returns at most `n` bytes (a reader that returns more is truncated). -/
def loop (read : USize → IO ByteArray) (cap : Nat) : Nat → ByteArray → IO ByteArray
  | 0, acc => pure acc
  | fuel + 1, acc => do
    if acc.size > cap then return acc
    let want := min chunkBytes (cap + 1 - acc.size)
    let chunk ← read want.toUSize
    if chunk.size == 0 then return acc
    -- A misbehaving reader cannot push the buffer past the budget.
    let chunk := if chunk.size ≤ want then chunk else chunk.extract 0 want
    loop read cap fuel (acc.append chunk)

/-- **Capped read over a chunk reader** (`read n` returns at most `n` bytes, empty at end of
input): the whole input when it has at most `cap` bytes, else `Error.limitExceeded kind`
after pulling at most `cap + 1` bytes. -/
def readWith (read : USize → IO ByteArray) (cap : Nat) (kind : LimitKind := .inputBytes) :
    IO (Except Error ByteArray) := do
  -- `cap + 2` calls suffice: each non-empty chunk adds ≥ 1 byte, the loop stops past `cap`.
  let bytes ← loop read cap (cap + 2) ByteArray.empty
  if bytes.size > cap then return .error (.limitExceeded kind)
  return .ok bytes

/-- **Capped read of an open handle** (`readWith` over `IO.FS.Handle.read`). -/
def readHandle (h : IO.FS.Handle) (cap : Nat) (kind : LimitKind := .inputBytes) :
    IO (Except Error ByteArray) :=
  readWith h.read cap kind

/-- **Capped read of the file `path`**: `.ok bytes` (the whole file, at most `cap` bytes) or
`Error.limitExceeded kind`. A file whose `stat` size is already above `cap` is rejected
without reading; otherwise the file is read through a handle with a budget of `cap + 1`
bytes, so a file that grows meanwhile is still rejected after at most `cap + 1` bytes.
File-system errors (missing, unreadable, a directory) are thrown as `IO` errors. -/
def readFile (path : System.FilePath) (cap : Nat) (kind : LimitKind := .inputBytes) :
    IO (Except Error ByteArray) := do
  let md ← path.metadata
  if md.byteSize.toNat > cap then return .error (.limitExceeded kind)
  let h ← IO.FS.Handle.mk path .read
  readHandle h cap kind

end SafePdf.Shell.Read
