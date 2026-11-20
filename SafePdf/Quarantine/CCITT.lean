import SafePdf.Core.Limits
import SafePdf.Core.Error

/-!
# CCITT Group 3/4 fax decoder (`/CCITTFaxDecode`, task 7.8)

Plan.md §3 (the quarantine zone: image codecs are decoded outside the trusted path and their
output is re-validated before it enters the core), §6 Phase 3 ("a failed image renders as a
placeholder box") and Phase 7 ("images composited from quarantine-zone decodes"). Like
`Quarantine.DCT`, this decoder is pure Lean written under the rules of `Core/` (no
`partial`, `unsafe`, `panic!`, `!` indexing, `sorry`); every loop runs on explicit fuel.

Found by task 7.8: dvips + Ghostscript Type 3 bitmap fonts draw each glyph as an inline
stencil mask `BI /IM true /D [1 0] /F /CCF /DP << /K -1 /Columns w >> ID … EI`; with the codec
missing the glyph was the placeholder, i.e. a solid box in the text colour.

ITU-T T.4 (Group 3, one- and two-dimensional) and T.6 (Group 4), ISO 32000-2 §7.4.6
(`/K`, `/EndOfLine`, `/EncodedByteAlign`, `/Columns`, `/Rows`, `/EndOfBlock`, `/BlackIs1`).
The reference is MuPDF 1.25.1 `source/fitz/filter-fax.c` (`next_faxd`), ported state for
state so that malformed data decodes as MuPDF decodes it:

* the code tables are MuPDF's two-level lookup tables (`cf_white_decode`,
  `cf_black_decode`, `cf_2d_decode`; first level 8, 7, 7 bits);
* bits past the end of the data read as zeros; decoding stops when every bit is consumed
  (a started row is emitted first), at `RTC`/`EOFB` (2 resp. 6 consecutive `EOL`s on an empty
  row), after `/Rows` rows when `/EndOfBlock` is false, or at the first invalid code (the
  partly decoded row is emitted, then decoding stops — MuPDF's `error:` label);
* uncompressed mode is an error (as in MuPDF);
* `/EndOfLine` true requires an initial `EOL` (searched bit by bit, else an error);
  `/EncodedByteAlign` aligns each row as MuPDF does (before the `EOL` when `/EndOfLine`);
* each row is `⌈Columns / 8⌉` bytes, `1` = black, inverted unless `/BlackIs1`.

## Bounds

At most `maxRows` rows are produced (the caller passes the image height: later rows are never
read); `⌈Columns / 8⌉ · maxRows ≤ Limits.maxDecodedStreamBytes` and
`Columns ≤ Limits.maxImagePixels`, else `Error.limitExceeded`. The main loop runs at most
once per input bit plus two (every iteration but the last one or two consumes a bit or
stops); a changing-element search scans at most one row.

## API

`decode limits params maxRows bytes : Except Error ByteArray` — the rows, concatenated; fewer
than `maxRows` rows when the data ends early (the image layer pads with zeros, as MuPDF
does).
-/

namespace SafePdf.Quarantine.CCITT

open SafePdf

/-- The `/CCITTFaxDecode` parameters (ISO 32000-2 Table 11), with MuPDF's defaults
(`pdf-stream.c` `build_compression_params`). -/
structure Params where
  /-- `/K`: `< 0` pure two-dimensional (Group 4), `0` one-dimensional, `> 0` mixed. -/
  k : Int := 0
  /-- `/EndOfLine`: rows start with an `EOL` code. -/
  endOfLine : Bool := false
  /-- `/EncodedByteAlign`: rows start on byte boundaries. -/
  byteAlign : Bool := false
  /-- `/Columns`. -/
  columns : Nat := 1728
  /-- `/Rows` (`0`: unknown). -/
  rows : Nat := 0
  /-- `/EndOfBlock`: data ends with `RTC`/`EOFB` (else after `/Rows` rows). -/
  endOfBlock : Bool := true
  /-- `/BlackIs1`: `1` bits are black in the output. -/
  blackIs1 : Bool := false
  deriving Repr, Inhabited

/-! ## 1. Code tables (MuPDF `filter-fax.c`) -/

/-- Parse a table literal: pairs `value bits`. -/
def parseTable (s : String) : Array (Int × Nat) :=
  let ns := ((s.splitOn " ").filter (· ≠ "")).filterMap String.toInt?
  let rec go : (fuel : Nat) → List Int → Array (Int × Nat) → Array (Int × Nat)
    | 0, _, acc => acc
    | _ + 1, [], acc => acc
    | _ + 1, [_], acc => acc
    | fuel + 1, v :: n :: rest, acc => go fuel rest (acc.push (v, n.toNat))
  go ns.length ns #[]

/-- White run lengths (first level 8 bits). `-1` error, `-2` zeros (EOL follows), `-3`
uncompressed; entries with more bits than the first level point to a second-level table. -/
def whiteTable : Array (Int × Nat) := parseTable "256 12 272 12 29 8 30 8 45 8 46 8 22 7 22 7 23 7 23 7 47 8 48 8 13 6 13 6 13 6 13 6 20 7 \
    20 7 33 8 34 8 35 8 36 8 37 8 38 8 19 7 19 7 31 8 32 8 1 6 1 6 1 6 1 6 12 6 12 6 12 6 12 \
    6 53 8 54 8 26 7 26 7 39 8 40 8 41 8 42 8 43 8 44 8 21 7 21 7 28 7 28 7 61 8 62 8 63 8 0 \
    8 320 8 384 8 10 5 10 5 10 5 10 5 10 5 10 5 10 5 10 5 11 5 11 5 11 5 11 5 11 5 11 5 11 5 \
    11 5 27 7 27 7 59 8 60 8 288 9 290 9 18 7 18 7 24 7 24 7 49 8 50 8 51 8 52 8 25 7 25 7 \
    55 8 56 8 57 8 58 8 192 6 192 6 192 6 192 6 1664 6 1664 6 1664 6 1664 6 448 8 512 8 292 \
    9 640 8 576 8 294 9 296 9 298 9 300 9 302 9 256 7 256 7 2 4 2 4 2 4 2 4 2 4 2 4 2 4 2 4 \
    2 4 2 4 2 4 2 4 2 4 2 4 2 4 2 4 3 4 3 4 3 4 3 4 3 4 3 4 3 4 3 4 3 4 3 4 3 4 3 4 3 4 3 4 \
    3 4 3 4 128 5 128 5 128 5 128 5 128 5 128 5 128 5 128 5 8 5 8 5 8 5 8 5 8 5 8 5 8 5 8 5 \
    9 5 9 5 9 5 9 5 9 5 9 5 9 5 9 5 16 6 16 6 16 6 16 6 17 6 17 6 17 6 17 6 4 4 4 4 4 4 4 4 \
    4 4 4 4 4 4 4 4 4 4 4 4 4 4 4 4 4 4 4 4 4 4 4 4 5 4 5 4 5 4 5 4 5 4 5 4 5 4 5 4 5 4 5 4 \
    5 4 5 4 5 4 5 4 5 4 5 4 14 6 14 6 14 6 14 6 15 6 15 6 15 6 15 6 64 5 64 5 64 5 64 5 64 5 \
    64 5 64 5 64 5 6 4 6 4 6 4 6 4 6 4 6 4 6 4 6 4 6 4 6 4 6 4 6 4 6 4 6 4 6 4 6 4 7 4 7 4 7 \
    4 7 4 7 4 7 4 7 4 7 4 7 4 7 4 7 4 7 4 7 4 7 4 7 4 7 4 -2 3 -2 3 -1 0 -1 0 -1 0 -1 0 -1 0 \
    -1 0 -1 0 -1 0 -1 0 -1 0 -1 0 -1 0 -1 0 -3 4 1792 3 1792 3 1984 4 2048 4 2112 4 2176 4 \
    2240 4 2304 4 1856 3 1856 3 1920 3 1920 3 2368 4 2432 4 2496 4 2560 4 1472 1 1536 1 1600 \
    1 1728 1 704 1 768 1 832 1 896 1 960 1 1024 1 1088 1 1152 1 1216 1 1280 1 1344 1 1408 1"

/-- Black run lengths (first level 7 bits). -/
def blackTable : Array (Int × Nat) := parseTable "128 12 160 13 224 12 256 12 10 7 11 7 288 12 12 7 9 6 9 6 8 6 8 6 7 5 7 5 7 5 7 5 6 4 6 \
    4 6 4 6 4 6 4 6 4 6 4 6 4 5 4 5 4 5 4 5 4 5 4 5 4 5 4 5 4 1 3 1 3 1 3 1 3 1 3 1 3 1 3 1 \
    3 1 3 1 3 1 3 1 3 1 3 1 3 1 3 1 3 4 3 4 3 4 3 4 3 4 3 4 3 4 3 4 3 4 3 4 3 4 3 4 3 4 3 4 \
    3 4 3 4 3 3 2 3 2 3 2 3 2 3 2 3 2 3 2 3 2 3 2 3 2 3 2 3 2 3 2 3 2 3 2 3 2 3 2 3 2 3 2 3 \
    2 3 2 3 2 3 2 3 2 3 2 3 2 3 2 3 2 3 2 3 2 3 2 3 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 \
    2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 2 \
    2 -2 4 -2 4 -1 0 -1 0 -1 0 -1 0 -1 0 -1 0 -1 0 -1 0 -1 0 -1 0 -1 0 -1 0 -1 0 -3 5 1792 4 \
    1792 4 1984 5 2048 5 2112 5 2176 5 2240 5 2304 5 1856 4 1856 4 1920 4 1920 4 2368 5 2432 \
    5 2496 5 2560 5 18 3 18 3 18 3 18 3 18 3 18 3 18 3 18 3 52 5 52 5 640 6 704 6 768 6 832 \
    6 55 5 55 5 56 5 56 5 1280 6 1344 6 1408 6 1472 6 59 5 59 5 60 5 60 5 1536 6 1600 6 24 4 \
    24 4 24 4 24 4 25 4 25 4 25 4 25 4 1664 6 1728 6 320 5 320 5 384 5 384 5 448 5 448 5 512 \
    6 576 6 53 5 53 5 54 5 54 5 896 6 960 6 1024 6 1088 6 1152 6 1216 6 64 3 64 3 64 3 64 3 \
    64 3 64 3 64 3 64 3 13 1 13 1 13 1 13 1 13 1 13 1 13 1 13 1 13 1 13 1 13 1 13 1 13 1 13 \
    1 13 1 13 1 23 4 23 4 50 5 51 5 44 5 45 5 46 5 47 5 57 5 58 5 61 5 256 5 16 3 16 3 16 3 \
    16 3 17 3 17 3 17 3 17 3 48 5 49 5 62 5 63 5 30 5 31 5 32 5 33 5 40 5 41 5 22 4 22 4 14 \
    1 14 1 14 1 14 1 14 1 14 1 14 1 14 1 14 1 14 1 14 1 14 1 14 1 14 1 14 1 14 1 15 2 15 2 \
    15 2 15 2 15 2 15 2 15 2 15 2 128 5 192 5 26 5 27 5 28 5 29 5 19 4 19 4 20 4 20 4 34 5 \
    35 5 36 5 37 5 38 5 39 5 21 4 21 4 42 5 43 5 0 3 0 3 0 3 0 3"

/-- Two-dimensional mode codes (first level 7 bits): `-4` pass, `-5` horizontal, `0 … 6`
vertical `VR3 VR2 VR1 V0 VL1 VL2 VL3`. -/
def twoDTable : Array (Int × Nat) := parseTable "128 11 144 10 6 7 0 7 5 6 5 6 1 6 1 6 -4 4 -4 4 -4 4 -4 4 -4 4 -4 4 -4 4 -4 4 -5 3 -5 3 \
    -5 3 -5 3 -5 3 -5 3 -5 3 -5 3 -5 3 -5 3 -5 3 -5 3 -5 3 -5 3 -5 3 -5 3 4 3 4 3 4 3 4 3 4 \
    3 4 3 4 3 4 3 4 3 4 3 4 3 4 3 4 3 4 3 4 3 4 3 2 3 2 3 2 3 2 3 2 3 2 3 2 3 2 3 2 3 2 3 2 \
    3 2 3 2 3 2 3 2 3 2 3 3 1 3 1 3 1 3 1 3 1 3 1 3 1 3 1 3 1 3 1 3 1 3 1 3 1 3 1 3 1 3 1 3 \
    1 3 1 3 1 3 1 3 1 3 1 3 1 3 1 3 1 3 1 3 1 3 1 3 1 3 1 3 1 3 1 3 1 3 1 3 1 3 1 3 1 3 1 3 \
    1 3 1 3 1 3 1 3 1 3 1 3 1 3 1 3 1 3 1 3 1 3 1 3 1 3 1 3 1 3 1 3 1 3 1 3 1 3 1 3 1 3 1 3 \
    1 3 1 3 1 3 1 -2 4 -1 0 -1 0 -1 0 -1 0 -1 0 -1 0 -1 0 -1 0 -1 0 -1 0 -1 0 -1 0 -1 0 -1 0 \
    -1 0 -1 0 -1 0 -1 0 -1 0 -1 0 -1 0 -1 0 -3 3"

/-! ## 2. Bits -/

/-- Byte `i` of `b` (`0` out of range). -/
@[inline] def rd (b : ByteArray) (i : Nat) : Nat := if h : i < b.size then (b.get i h).toNat else 0

/-- The `n ≤ 32` bits of `b` starting at bit `pos` (most significant first), bits past the
end read as zeros. -/
def peek (b : ByteArray) (pos n : Nat) : Nat :=
  let i := pos / 8
  let w := (((rd b i * 256 + rd b (i + 1)) * 256 + rd b (i + 2)) * 256 + rd b (i + 3)) * 256
    + rd b (i + 4)
  (w >>> (40 - pos % 8 - n)) % (2 ^ n)

/-- Pixel `x` of a row (`0` for `x < 0` or out of range). -/
@[inline] def bit (line : ByteArray) (x : Int) : Nat :=
  if x < 0 then 0 else
  let x := x.toNat
  (rd line (x / 8) >>> (7 - x % 8)) % 2

/-- Look up a code: `(value, bits used)` (`(-1, 0)` out of range). -/
def getCode (b : ByteArray) (pos : Nat) (table : Array (Int × Nat)) (initial : Nat) :
    Int × Nat :=
  let (v, n) := table.getD (peek b pos initial) (-1, 0)
  if initial < n then
    let i := v + ((peek b pos n % 2 ^ (n - initial) : Nat) : Int)
    let (v2, n2) := table.getD i.toNat (-1, 0)
    (if i < 0 then (-1, initial) else (v2, initial + n2))
  else (v, n)

/-- The first changing element after `x` (from position 0 when `x < 0`, the pixel before
being white), within `w` columns, else `w` (MuPDF `find_changing`). `fuel` columns are
scanned at most. -/
def findChangingFrom (line : ByteArray) (w : Nat) : (fuel p : Nat) → Nat
  | 0, _ => w
  | fuel + 1, p =>
    if w ≤ p then w
    else
      let prev := bit line ((p : Int) - 1)
      -- whole bytes without a transition are skipped
      if p % 8 = 0 ∧ p + 8 ≤ w ∧ rd line (p / 8) = (if prev = 1 then 255 else 0) then
        findChangingFrom line w fuel (p + 8)
      else if bit line p ≠ prev then p
      else findChangingFrom line w fuel (p + 1)

/-- MuPDF `find_changing`. -/
def findChanging (line : ByteArray) (x : Int) (w : Nat) : Nat :=
  findChangingFrom line w (w + 1) (if x < 0 then 0 else x.toNat + 1)

/-- MuPDF `find_changing_color`: the next changing element after `x` of colour `color`. -/
def findChangingColor (line : ByteArray) (x : Int) (w : Nat) (color : Nat) : Nat :=
  if (w : Int) ≤ x then w else
  let x' := findChanging line (if 0 < x ∨ color = 0 then x else -1) w
  if x' < w ∧ bit line x' ≠ color then findChanging line x' w else x'

/-- Set the pixels `[x0, x1)` of a row (MuPDF `setbits`). -/
def setBitsFrom (x1 : Nat) : (fuel x : Nat) → ByteArray → ByteArray
  | 0, _, line => line
  | fuel + 1, x, line =>
    if x1 ≤ x then line
    else if x % 8 = 0 ∧ x + 8 ≤ x1 then
      setBitsFrom x1 fuel (x + 8) (if h : x / 8 < line.size then line.set (x / 8) 255 h else line)
    else
      let i := x / 8
      let line := if h : i < line.size then
        line.set i (line.get i h ||| (UInt8.ofNat (128 >>> (x % 8)))) h else line
      setBitsFrom x1 fuel (x + 1) line

/-- Set the pixels `[x0, x1)` (negative `x0` from 0). -/
def setBits (line : ByteArray) (x0 x1 : Int) : ByteArray :=
  if x1 ≤ x0 then line else
  let s := if x0 < 0 then 0 else x0.toNat
  setBitsFrom x1.toNat (x1.toNat + 1) s line

/-! ## 3. The decoder state machine (MuPDF `next_faxd`) -/

/-- Within-row stage (MuPDF `STATE_NORMAL`, `STATE_MAKEUP`, `STATE_H1`, `STATE_H2`). -/
inductive Stage where
  | normal | makeup | h1 | h2
  deriving DecidableEq, Repr, Inhabited

/-- Decoder state. -/
structure St where
  /-- Bits consumed. -/
  pos : Nat
  /-- Current position in the row (`-1` before the first code). -/
  a : Int
  /-- Current colour is black. -/
  c : Bool
  /-- Within-row stage. -/
  stage : Stage
  /-- Coding of the current row: 1 or 2 dimensions. -/
  dim : Nat
  /-- Consecutive `EOL`s. -/
  eolc : Nat
  /-- Rows completed. -/
  ridx : Nat
  /-- Reference (previous) row. -/
  ref : ByteArray
  /-- Row being decoded. -/
  dst : ByteArray
  /-- Output rows. -/
  out : ByteArray

/-- Output bytes of a row: as decoded with `/BlackIs1`, else inverted. -/
def rowBytes (p : Params) (row : ByteArray) : ByteArray :=
  if p.blackIs1 then row else ⟨row.data.map (· ^^^ 255)⟩

/-- A one-dimensional code (MuPDF `dec1d`); `none` on an invalid code or overflow. -/
def dec1d (p : Params) (b : ByteArray) (st : St) : Option St :=
  let a := if st.a = -1 then 0 else st.a
  let (code, n) := if st.c then getCode b st.pos blackTable 7 else getCode b st.pos whiteTable 8
  let st := { st with pos := st.pos + n }
  if code < 0 then none
  else if (p.columns : Int) < a + code then none
  else
    let dst := if st.c then setBits st.dst a (a + code) else st.dst
    let st := { st with dst, a := a + code }
    if code < 64 then some { st with c := !st.c, stage := .normal }
    else some { st with stage := .makeup }

/-- A vertical-mode step to `b1` (MuPDF `V0`, `VRn`, `VLn`). -/
def vstep (st : St) (b1 : Int) : St :=
  { st with dst := if st.c then setBits st.dst st.a b1 else st.dst, a := b1, c := !st.c }

/-- A two-dimensional code (MuPDF `dec2d`); `none` on an invalid code or overflow. -/
def dec2d (p : Params) (b : ByteArray) (st : St) : Option St :=
  let w := p.columns
  if st.stage = .h1 ∨ st.stage = .h2 then
    let a := if st.a = -1 then 0 else st.a
    let (code, n) := if st.c then getCode b st.pos blackTable 7 else getCode b st.pos whiteTable 8
    let st := { st with pos := st.pos + n }
    if code < 0 then none
    else if (w : Int) < a + code then none
    else
      let dst := if st.c then setBits st.dst a (a + code) else st.dst
      let st := { st with dst, a := a + code }
      if code < 64 then
        some { st with c := !st.c, stage := if st.stage = .h1 then .h2 else .normal }
      else some st
  else
    let (code, n) := getCode b st.pos twoDTable 7
    let st := { st with pos := st.pos + n }
    let color := if st.c then 0 else 1
    if code = -5 then some { st with stage := .h1 }
    else
    let b1 : Int := findChangingColor st.ref st.a w color
    if code = -4 then
      let b2 : Int := if (w : Int) ≤ b1 then w else findChanging st.ref b1 w
      some { st with dst := if st.c then setBits st.dst st.a b2 else st.dst, a := b2 }
    else if code = 3 then some (vstep st b1)
    else if 0 ≤ code ∧ code < 3 then some (vstep st (min (b1 + (3 - code)) w))
    else if 3 < code ∧ code ≤ 6 then some (vstep st (max (b1 - (code - 3)) 0))
    else none

/-- Outcome of one loop iteration. -/
inductive Step where
  /-- Go on. -/
  | cont (st : St)
  /-- Decoding finished with these output rows. -/
  | done (out : ByteArray)

/-- End of a row (MuPDF `eol:`): emit it, swap rows, prepare the next one. -/
def eol (p : Params) (maxRows : Nat) (st : St) : Step :=
  let out := st.out ++ rowBytes p st.dst
  let ridx := st.ridx + 1
  if maxRows ≤ ridx then .done out
  else if !p.endOfBlock ∧ 0 < p.rows ∧ p.rows ≤ ridx then .done out
  else
    let stride := (p.columns + 7) / 8
    let dim := if 0 < p.k ∧ st.eolc = 0 then
        (if (ridx : Int) % p.k = 0 then 1 else 2) else st.dim
    let pos := if p.byteAlign then
        (if p.endOfLine then st.pos + (12 - st.pos % 8) % 8 else st.pos + (8 - st.pos % 8) % 8)
      else st.pos
    .cont { st with out, ridx, ref := st.dst, dst := ⟨Array.replicate stride 0⟩,
                    stage := .normal, c := false, a := -1, dim, pos }

/-- One iteration of MuPDF's `loop:`. -/
def step (p : Params) (maxRows : Nat) (b : ByteArray) (st : St) : Step :=
  if b.size * 8 ≤ st.pos then
    if 0 < st.a then eol p maxRows st else .done st.out
  else
    let w12 := peek b st.pos 12
    if w12 = 0 then .cont { st with pos := st.pos + 1 }
    else
      let r : Option St :=
        if w12 = 1 then
          let st := { st with pos := st.pos + 12, eolc := st.eolc + 1 }
          if 0 < p.k then
            some { st with a := if st.a = -1 then 0 else st.a,
                           dim := if peek b st.pos 1 = 1 then 1 else 2, pos := st.pos + 1 }
          else some st
        else if 0 < p.k ∧ st.a = -1 then
          some { st with a := 0, dim := if peek b st.pos 1 = 1 then 1 else 2, pos := st.pos + 1 }
        else if st.dim = 1 then dec1d p b { st with eolc := 0 }
        else dec2d p b { st with eolc := 0 }
      match r with
      | none => .done (st.out ++ rowBytes p st.dst)
      | some st =>
        if st.stage ≠ .normal then .cont st
        else if 0 < st.eolc ∨ (p.columns : Int) ≤ st.a then
          if 0 < st.a then eol p maxRows st
          else if st.eolc = (if p.k < 0 then 2 else 6) then .done st.out
          else .cont st
        else .cont st

/-- Run the loop on `fuel` iterations (out of fuel: the rows so far). -/
def run (p : Params) (maxRows : Nat) (b : ByteArray) : (fuel : Nat) → St → ByteArray
  | 0, st => st.out
  | fuel + 1, st =>
    match step p maxRows b st with
    | .done out => out
    | .cont st => run p maxRows b fuel st

/-- The initial `EOL` search (`/EndOfLine`): skip bits while at least 13 remain and the next
12 are not `EOL`; `none` when no `EOL` is found. -/
def seekEol (b : ByteArray) : (fuel pos : Nat) → Option Nat
  | 0, _ => none
  | fuel + 1, pos =>
    if peek b pos 12 = 1 then some pos
    else if b.size * 8 < pos + 13 then none
    else seekEol b fuel (pos + 1)

/-- **Decode CCITT fax data**: at most `maxRows` rows of `⌈Columns / 8⌉` bytes. -/
def decode (limits : Limits) (p : Params) (maxRows : Nat) (b : ByteArray) :
    Except Error ByteArray :=
  if limits.maxImagePixels < p.columns then .error (.limitExceeded .imagePixels)
  else
  let stride := (p.columns + 7) / 8
  if limits.maxDecodedStreamBytes < stride * maxRows then
    .error (.limitExceeded .decodedStreamBytes)
  else if p.columns = 0 ∨ maxRows = 0 then .ok ByteArray.empty
  else
    let start : Option Nat :=
      if p.endOfLine then seekEol b (b.size * 8 + 1) 0 else some 0
    match start with
    | none => .error (.malformed 0 "CCITTFax: initial EOL not found")
    | some pos =>
      let zero : ByteArray := ⟨Array.replicate stride 0⟩
      .ok (run p maxRows b (b.size * 8 + 3)
        { pos, a := -1, c := false, stage := .normal, dim := if p.k < 0 then 2 else 1,
          eolc := 0, ridx := 0, ref := zero, dst := zero, out := ByteArray.empty })

end SafePdf.Quarantine.CCITT
