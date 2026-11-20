import SafePdf.Core.Error
import SafePdf.Core.Limits
import SafePdf.Core.Object
import SafePdf.Core.Content.GState
import SafePdf.Core.Font.Outline

/-!
# Embedded CFF fonts: metrics and mapping (Plan.md §6 Phase 6, task 6.2; Adobe TN #5176, #5177)

Parses a Compact Font Format font program as embedded in PDF (ISO 32000-2 §9.9 `/FontFile3`
with `/Subtype /Type1C` for simple fonts and `/CIDFontType0C` for CIDFonts, already
Flate-decoded by the caller) far enough to give **text extraction and glyph positions** what
they need: the font name, `FontMatrix`, `FontBBox`, the charset (glyph names or CIDs), the
encoding (code ↦ glyph), and each glyph's advance width from its Type 2 charstring.
Outlines (task 7.3a): `CFFFont.outline` re-runs a charstring with path recording
(`CState.record`; all Type 2 path operators, the flex family, the `endchar` accent form).
References: *The Compact Font Format Specification* (Adobe Technical
Note #5176, 2003) §§ 4–19 and *The Type 2 Charstring Format* (TN #5177, 2000) §§ 3–4.

Fonts are untrusted input (Plan.md §6), so this module follows the core discipline: pure,
every loop structural (over a count read from the font and bounded by a cap or the input) or
decreasing on `size - position`, every byte read bounds-checked (`bs[i]?`, `extract`), every
charstring run fuel-bounded.

## Pipeline

1. Header (§6): major version 1 (`2` is CFF2, unsupported), `hdrSize`.
2. Name, Top DICT, String and Global Subr INDEXes (§5, §8–§10) via `parseIndex`, which
   validates offset size, count cap, first offset `1`, monotone offsets and that the data
   ends inside the input; the result carries these facts (`Index.Valid`).
3. Top DICT (`parseDict`, §4 Table 3, §9): integers, reals (nibble form, at most
   `maxRealDigits` digits and exponent `≤ maxRealExp`), at most `maxDictOperands` operands.
   Used keys: `FontMatrix` (12 7), `FontBBox` (5), `charset` (15), `Encoding` (16),
   `CharStrings` (17), `Private` (18), `CharstringType` (12 6, must be 2), and for CID-keyed
   fonts `ROS` (12 30), `FDArray` (12 36), `FDSelect` (12 37).
4. Private DICTs (§15): `Subrs` (19, offset relative to the Private DICT), `defaultWidthX`
   (20), `nominalWidthX` (21). A CID-keyed font has one per Font DICT of its `FDArray`.
5. charset (§13) formats 0/1/2 and the predefined ISOAdobe/Expert/ExpertSubset charsets: GID ↦
   SID (name-keyed) or CID. For a CID-keyed font, offsets 0–2 mean the identity.
6. Encoding (§12) formats 0/1 with supplements, and the predefined Standard (0) and Expert (1)
   encodings (code ↦ SID ↦ GID through the charset): code ↦ GID. CID-keyed fonts have none.
7. FDSelect (§19) formats 0 and 3 (ranges must start at 0 and increase): GID ↦ Font DICT.
8. `run`: the Type 2 charstring interpreter for metrics (TN #5177 §4). It executes every
   operator (to validate the charstring) but only records the width and the `endchar`
   accent form; path operators only clear the stack. Width rule (§3.1): the first
   stack-clearing operator (`hstem[hm]`, `vstem[hm]`, `hintmask`, `cntrmask`, `rmoveto`,
   `hmoveto`, `vmoveto`, `endchar`) may have one extra operand at the bottom of the stack,
   the width relative to `nominalWidthX`; without it the width is `defaultWidthX`.
   `hintmask`/`cntrmask` skip `⌈stems/8⌉` mask bytes (stems counted from the stem hints,
   including the implicit `vstem` operands before the first mask). `callsubr`/`callgsubr`
   add the bias (107, 1131 or 32768 by subr count, §4.7). Reaching the end of a subroutine
   without `return` returns implicitly (as FreeType does); reaching the end of the glyph's own
   charstring without `endchar` rejects it. `endchar` with 4 extra operands (the deprecated
   `seac`-like accent form, TN #5177 Appendix C) records the base and accent codes
   (Standard Encoding codes).
   Supported arithmetic (§4.5): `abs add sub div neg mul eq and or not drop dup exch`; the
   rarely used `put get ifelse random sqrt index roll` reject the glyph, as do reserved
   operators and the CFF2 `vsindex`/`blend`.

## Bounds and caps

Resource caps come from `Limits` (task 6.2b): `maxCFFGlyphs` (default 65535, the 16-bit
INDEX count) charstrings, else `Error.limitExceeded .fontGlyphs`; `maxFontSubrs` (default
32768) entries per Global or local Subrs INDEX, else `.fontSubrs`; `maxFontDicts` (default
256) Font DICTs in the `FDArray`, else `.fontDicts`; `glyphFuel` (20000) steps per glyph; and
a **font-wide** charstring budget `fontFuel` (2²⁵) steps: once it is spent, the remaining
glyphs are rejected (not fatal, like `glyphFuel`), so parsing a font costs at most `fontFuel`
interpreter steps however many glyphs it has. A glyph that fails is charged the whole fuel it
was given. Format constants stay local (exceeding them is `Error.malformed`): argument stack
`maxStack = 48` (TN #5177 App. B), subroutine nesting `maxCallDepth = 10`, DICT operands
`maxDictOperands = 48`, the 16-bit Name/Top/String INDEX counts `maxStrings`. Input ≤ `Limits.maxDecodedStreamBytes`. For scale: the
twelve Source Sans Pro 3.006 CFFs (1795–2194 glyphs) need about 200 000 steps in all, at most
322 for one glyph, and every width matches their `hmtx` table.

## What is skipped

Hint semantics, `put get ifelse random sqrt index roll`, CFF2 and
OpenType-wrapped CFF (`/FontFile3 /Subtype /OpenType`), synthetic fonts, multiple fonts in one
FontSet (the first is used), `Encoding` for CID-keyed fonts (ignored, as the spec says).

A glyph is **rejected** (listed in `CFFFont.rejected`, never fatal) on: stack overflow or
underflow, nesting deeper than `maxCallDepth`, a bad subroutine index, a reserved or
unsupported operator, a truncated number or hint mask, division by zero, running off the end
without `endchar`, fuel exhaustion, a bad `endchar` accent code, or an FDSelect entry naming a
missing Font DICT. The font fails only if no glyph is valid or its structure is broken.

## Results

`CFFFont` holds the GID-indexed glyph table (size as a proof field), the charset, the 256-entry
code ↦ GID encoding (size as a proof field) and the inverse charset (SID/CID ↦ GID).
`advanceOfGid`, `advance code` (simple fonts, through the encoding) and `advanceOfCID` give the
text-space advance: the glyph-space width times the `a` entry of the effective font matrix
(for CID-keyed fonts the Font DICT's matrix composed with the Top DICT's), computed exactly
from the `Decimal` entries and rounded once to `Fixed` — what
`Core.Content.Interp.Config.advance` consumes. `glyphName?`/`glyphNameOfCode` give the glyph
name (standard strings or the String INDEX) so text extraction can map through the AGL.

## Theorems

`readBE_lt` (an offset of `n` bytes is `< 256ⁿ`); `Index.item_end_le` (every INDEX item lies
inside the input) and `Index.count_le` (parsed counts respect their caps), both from
`Index.Valid` which `parseIndex` establishes by construction; `bias_pos`; `run_stack_le`,
`run_calls_le`, `run_steps_le` (stack bound, nesting bound and step bound of the charstring
interpreter: the fuel it reports left never exceeds the fuel given); `evalList_size` (one glyph
entry per charstring); `CFFFont.numGlyphs_le_max`; `CFFFont.advance_eq`.
-/

namespace SafePdf.Core.Font.CFF

open SafePdf SafePdf.Core.Content

/-! ## Caps -/

/-- Maximum Type 2 argument-stack depth (TN #5177 Appendix B: 48). -/
def maxStack : Nat := 48

/-- Maximum subroutine nesting (TN #5177 Appendix B: 10). -/
def maxCallDepth : Nat := 10

/-- Maximum number of entries in the Name, Top DICT and String INDEXes: the format's own
bound (INDEX counts and SIDs are 16-bit), so it never rejects a well-formed font. -/
def maxStrings : Nat := 65535

/-- Maximum operands before one DICT operator (TN #5176 Appendix B: 48). -/
def maxDictOperands : Nat := 48

/-- Maximum significand digits of a DICT real number. -/
def maxRealDigits : Nat := 20

/-- Maximum absolute decimal exponent of a DICT real number. -/
def maxRealExp : Nat := 30

/-- The number of predefined standard strings (SIDs `0 … 390`). -/
def nStdStrings : Nat := 391


/-! ## Byte readers -/

/-- The byte at `i`, as a `Nat`. -/
def u8 (b : ByteArray) (i : Nat) : Option Nat := b[i]?.map (·.toNat)

/-- A big-endian 16-bit value at `i`. -/
def u16 (b : ByteArray) (i : Nat) : Option Nat := do
  let x ← u8 b i
  let y ← u8 b (i + 1)
  pure (x * 256 + y)

/-- A big-endian value of `n` bytes at `i`, accumulated onto `acc`. -/
def readBE (b : ByteArray) : Nat → Nat → Nat → Option Nat
  | _, 0, acc => some acc
  | i, n + 1, acc => (u8 b i).bind fun x => readBE b (i + 1) n (acc * 256 + x)

/-- A byte value is below 256. -/
theorem u8_lt {b : ByteArray} {i v : Nat} (h : u8 b i = some v) : v < 256 := by
  unfold u8 at h
  cases hb : b[i]? with
  | none => simp [hb] at h
  | some x =>
    simp only [hb, Option.map_some, Option.some.injEq] at h
    have := x.toNat_lt; omega

/-- **Offset bound**: a big-endian value of `n` bytes read onto `acc` is `< (acc + 1)·256ⁿ`; in
particular an INDEX offset of `offSize` bytes is `< 256 ^ offSize`. -/
theorem readBE_lt (b : ByteArray) :
    ∀ (n i acc v : Nat), readBE b i n acc = some v → v < (acc + 1) * 256 ^ n := by
  intro n
  induction n with
  | zero =>
    intro i acc v h
    simp only [readBE, Option.some.injEq] at h
    simp only [Nat.pow_zero, Nat.mul_one]; omega
  | succ n ih =>
    intro i acc v h
    simp only [readBE] at h
    cases hx : u8 b i with
    | none => simp [hx] at h
    | some x =>
      simp only [hx, Option.bind_some] at h
      have h1 := ih _ _ _ h
      have hx' := u8_lt hx
      have h3 : (acc * 256 + x + 1) * 256 ^ n ≤ ((acc + 1) * 256) * 256 ^ n :=
        Nat.mul_le_mul_right _ (by rw [Nat.add_mul]; omega)
      have h4 : ((acc + 1) * 256) * 256 ^ n = (acc + 1) * 256 ^ (n + 1) := by
        rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 256 (256 ^ n)]
      omega

/-- A signed 16-bit value. -/
def toI16 (v : Nat) : Int := if v < 32768 then (v : Int) else (v : Int) - 65536

/-- A signed 32-bit value. -/
def toI32 (v : Nat) : Int := if v < 2147483648 then (v : Int) else (v : Int) - 4294967296

/-- Bytes as a string, one character per byte (always valid). -/
def latin1 (b : ByteArray) : String := String.ofList (b.toList.map fun x => Char.ofNat x.toNat)

/-- Turn an internal error message into a `SafePdf.Error`. -/
def liftE {α : Type} : Except String α → Except Error α
  | .ok a => .ok a
  | .error e => .error (.malformed 0 ("CFF: " ++ e))

/-! ## INDEX (§5) -/

/-- A parsed INDEX: item `i` occupies `[dataBase + offsets[i], dataBase + offsets[i+1])` of the
input (offsets are 1-based, so `dataBase` is the position just before the data). -/
structure Index where
  /-- Number of items. -/
  count : Nat
  /-- Position before the first data byte. -/
  dataBase : Nat
  /-- The `count + 1` offsets. -/
  offsets : Array Nat
  /-- Position after the INDEX. -/
  endPos : Nat

/-- What `parseIndex` guarantees about an INDEX of an input of `size` bytes under count cap
`cap`. -/
def Index.Valid (size cap : Nat) (ix : Index) : Prop :=
  ix.count ≤ cap ∧ ix.offsets.size = ix.count + 1 ∧ ix.endPos ≤ size ∧
  ∀ (i : Nat) (h : i < ix.offsets.size), ix.dataBase + ix.offsets[i] ≤ ix.endPos

/-- Read `n` offsets of `offSize` bytes from `pos`, appending to `acc`. -/
def readOffsets (b : ByteArray) (offSize : Nat) : Nat → Nat → Array Nat → Option (Array Nat)
  | _, 0, acc => some acc
  | pos, n + 1, acc =>
    (readBE b pos offSize 0).bind fun o => readOffsets b offSize (pos + offSize) n (acc.push o)

/-- Whether a list of offsets is non-decreasing. -/
def monotone : List Nat → Bool
  | a :: b :: r => a ≤ b && monotone (b :: r)
  | _ => true

/-- Parse the INDEX at `pos` with at most `cap` items (§5). The result carries `Index.Valid`:
the count respects the cap and every item lies inside the input. -/
def parseIndex (b : ByteArray) (pos cap : Nat) :
    Except String {ix : Index // ix.Valid b.size cap} :=
  match u16 b pos with
  | none => .error "truncated INDEX"
  | some count =>
    if count = 0 then
      let ix : Index := ⟨0, pos + 1, #[1], pos + 2⟩
      if h : pos + 2 ≤ b.size then
        .ok ⟨ix, Nat.zero_le _, rfl, h, by
          intro i hi
          have : i = 0 := by simp only [ix, List.size_toArray, List.length_cons,
            List.length_nil] at hi; omega
          subst this; simp [ix]⟩
      else .error "truncated INDEX"
    else if hc : count ≤ cap then
      match u8 b (pos + 2) with
      | none => .error "truncated INDEX"
      | some offSize =>
        if 1 ≤ offSize ∧ offSize ≤ 4 then
          match readOffsets b offSize (pos + 3) (count + 1) #[] with
          | none => .error "truncated INDEX offsets"
          | some offs =>
            let dataBase := pos + 3 + (count + 1) * offSize - 1
            let endPos := dataBase + (offs[count]?).getD 0
            if offs[0]? = some 1 ∧ monotone offs.toList then
              if h : offs.size = count + 1 ∧ endPos ≤ b.size ∧
                  (offs.all fun o => decide (dataBase + o ≤ endPos)) = true then
                .ok ⟨⟨count, dataBase, offs, endPos⟩, hc, h.1, h.2.1, by
                  intro i hi
                  have := Array.all_eq_true.mp h.2.2 i hi
                  simpa using this⟩
              else .error "INDEX data out of bounds"
            else .error "INDEX offsets not increasing from 1"
        else .error "bad INDEX offSize"
    else .error s!"INDEX has more than {cap} items"

/-- Parse the INDEX at `pos` under a **resource limit** `cap` (a `Limits` field): an INDEX
whose count exceeds `cap` is `Error.limitExceeded kind`; other defects are `malformed`. -/
def limitIndex (b : ByteArray) (pos cap : Nat) (kind : LimitKind) :
    Except Error {ix : Index // ix.Valid b.size cap} :=
  match u16 b pos with
  | some count => if cap < count then .error (.limitExceeded kind) else liftE (parseIndex b pos cap)
  | none => liftE (parseIndex b pos cap)

/-- Item `i` of an INDEX. -/
def Index.item (b : ByteArray) (ix : Index) (i : Nat) : Option ByteArray :=
  match ix.offsets[i]?, ix.offsets[i + 1]? with
  | some s, some e => some (b.extract (ix.dataBase + s) (ix.dataBase + e))
  | _, _ => none

/-- All items of an INDEX (`count` of them). -/
def Index.items (b : ByteArray) (ix : Index) : Array ByteArray :=
  Array.ofFn (n := ix.count) fun i => (ix.item b i.val).getD ByteArray.empty

/-- **INDEX bounds**: in a valid INDEX, every item boundary lies inside the input. -/
theorem Index.item_end_le {size cap : Nat} {ix : Index} (hv : ix.Valid size cap) {i : Nat}
    (hi : i < ix.offsets.size) : ix.dataBase + ix.offsets[i] ≤ size :=
  Nat.le_trans (hv.2.2.2 i hi) hv.2.2.1

/-- **Count cap**: a valid INDEX has at most `cap` items. -/
theorem Index.count_le {size cap : Nat} {ix : Index} (hv : ix.Valid size cap) : ix.count ≤ cap :=
  hv.1

/-- `Index.items` has one entry per item. -/
theorem Index.items_size (b : ByteArray) (ix : Index) : (ix.items b).size = ix.count :=
  Array.size_ofFn

/-! ## DICT data (§4) -/

/-- Accumulator of the nibble form of a DICT real number (§4 Table 5). -/
structure RealAcc where
  /-- Significand digits read so far. -/
  mant : Nat := 0
  /-- Number of significand digits. -/
  digits : Nat := 0
  /-- Digits after the decimal point. -/
  frac : Nat := 0
  /-- A decimal point was read. -/
  point : Bool := false
  /-- A leading minus was read. -/
  neg : Bool := false
  /-- An exponent marker was read. -/
  inExp : Bool := false
  /-- The exponent is negative. -/
  expNeg : Bool := false
  /-- The exponent (saturated just above `maxRealExp`). -/
  exp : Nat := 0
  /-- The number is malformed or out of range. -/
  bad : Bool := false

/-- Process one nibble other than the end marker `f`. -/
def realNibble (a : RealAcc) (n : Nat) : RealAcc :=
  if n ≤ 9 then
    if a.inExp then
      let e := a.exp * 10 + n
      { a with exp := min e (maxRealExp + 1), bad := a.bad || maxRealExp < e }
    else if maxRealDigits ≤ a.digits then { a with bad := true }
    else { a with mant := a.mant * 10 + n, digits := a.digits + 1,
                  frac := if a.point then a.frac + 1 else a.frac }
  else if n == 10 then
    if a.point || a.inExp then { a with bad := true } else { a with point := true }
  else if n == 11 || n == 12 then
    if a.inExp then { a with bad := true } else { a with inExp := true, expNeg := n == 12 }
  else if n == 14 then
    if a.digits != 0 || a.point || a.inExp || a.neg then { a with bad := true }
    else { a with neg := true }
  else { a with bad := true }

/-- The exact value of a finished real number. -/
def RealAcc.toDecimal (a : RealAcc) : Decimal :=
  let m : Int := if a.neg then -(a.mant : Int) else a.mant
  if a.expNeg then Decimal.normalize ⟨m, a.frac + a.exp⟩
  else if a.frac ≤ a.exp then Decimal.normalize ⟨m * ((10 ^ (a.exp - a.frac) : Nat) : Int), 0⟩
  else Decimal.normalize ⟨m, a.frac - a.exp⟩

/-- Parse the nibbles of a real number from `pos` up to the end nibble `f`; returns the value
and the position after the byte holding `f`. -/
def parseReal (d : ByteArray) (pos : Nat) (a : RealAcc) : Option (Decimal × Nat) :=
  if h : pos < d.size then
    let byte := d[pos].toNat
    let hi := byte / 16
    let lo := byte % 16
    let fin (r : RealAcc) : Option (Decimal × Nat) :=
      if r.bad || r.digits == 0 then none else some (r.toDecimal, pos + 1)
    if hi == 15 then fin a
    else
      let a1 := realNibble a hi
      if lo == 15 then fin a1 else parseReal d (pos + 1) (realNibble a1 lo)
  else none
termination_by d.size - pos

/-- Decode the DICT operand starting with byte `v` at `pos` (§4 Table 3): the value and the
position after it. -/
def dictNum (d : ByteArray) (pos v : Nat) : Option (Decimal × Nat) :=
  if 32 ≤ v ∧ v ≤ 246 then some (⟨(v : Int) - 139, 0⟩, pos + 1)
  else if 247 ≤ v ∧ v ≤ 250 then
    (u8 d (pos + 1)).map fun w => (⟨((v - 247) * 256 + w + 108 : Nat), 0⟩, pos + 2)
  else if 251 ≤ v ∧ v ≤ 254 then
    (u8 d (pos + 1)).map fun w => (⟨-(((v - 251) * 256 + w + 108 : Nat) : Int), 0⟩, pos + 2)
  else if v == 28 then (u16 d (pos + 1)).map fun w => (⟨toI16 w, 0⟩, pos + 3)
  else if v == 29 then (readBE d (pos + 1) 4 0).map fun w => (⟨toI32 w, 0⟩, pos + 5)
  else if v == 30 then parseReal d (pos + 1) {}
  else none

/-- A DICT entry: operator key (escaped operators `12 w` as `1200 + w`) and its operands in
order. -/
abbrev DictEntry := Nat × List Decimal

/-- Parse DICT data from `pos`; `ops` holds the pending operands (top first). -/
def parseDict (d : ByteArray) (pos : Nat) (ops : List Decimal) (acc : List DictEntry) :
    Except String (List DictEntry) :=
  if h : pos < d.size then
    let v := d[pos].toNat
    if v ≤ 21 then
      if v == 12 then
        match u8 d (pos + 1) with
        | none => .error "truncated DICT escape operator"
        | some w => parseDict d (pos + 2) [] ((1200 + w, ops.reverse) :: acc)
      else parseDict d (pos + 1) [] ((v, ops.reverse) :: acc)
    else
      match dictNum d pos v with
      | none => .error "bad DICT operand"
      | some (x, pos') =>
        if pos < pos' then
          if ops.length < maxDictOperands then parseDict d pos' (x :: ops) acc
          else .error "too many DICT operands"
        else .error "bad DICT operand"
  else if ops.isEmpty then .ok acc.reverse else .error "DICT ends with operands"
termination_by d.size - pos

/-- The operands of the first entry with key `k`. -/
def dictGet (es : List DictEntry) (k : Nat) : Option (List Decimal) :=
  (es.find? (·.1 == k)).map (·.2)

/-- An integral decimal as an `Int`. -/
def decToInt? (x : Decimal) : Option Int :=
  let n := x.normalize
  if n.scale == 0 then some n.mantissa else none

/-- A non-negative integral decimal as a `Nat`. -/
def decToNat? (x : Decimal) : Option Nat :=
  (decToInt? x).bind fun i => if 0 ≤ i then some i.toNat else none

/-- Exact product of two decimals. -/
def decMul (x y : Decimal) : Decimal :=
  Decimal.normalize ⟨x.mantissa * y.mantissa, x.scale + y.scale⟩

/-- Exact sum of two decimals. -/
def decAdd (x y : Decimal) : Decimal :=
  let s := max x.scale y.scale
  Decimal.normalize ⟨x.mantissa * ((10 ^ (s - x.scale) : Nat) : Int) +
    y.mantissa * ((10 ^ (s - y.scale) : Nat) : Int), s⟩

/-- The single non-negative integer operand of key `k`, or `dflt` when absent. -/
def dictNat (es : List DictEntry) (k dflt : Nat) : Except String Nat :=
  match dictGet es k with
  | none => .ok dflt
  | some [x] => match decToNat? x with
    | some n => .ok n
    | none => .error s!"DICT operator {k}: expected a non-negative integer"
  | some _ => .error s!"DICT operator {k}: expected one operand"

/-- The default `FontMatrix` `[0.001 0 0 0.001 0 0]`. -/
def defaultMatrix : List Decimal :=
  [⟨1, 3⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 3⟩, ⟨0, 0⟩, ⟨0, 0⟩]

/-- The `FontMatrix` (12 7) of a DICT, if present with six operands. -/
def dictMatrix? (es : List DictEntry) : Except String (Option (List Decimal)) :=
  match dictGet es 1207 with
  | none => .ok none
  | some m => if m.length == 6 then .ok (some m) else .error "FontMatrix needs 6 operands"

/-! ## Predefined data (TN #5176 Appendices A–C)

Generated from the tables of fontTools 4.53.1 (`cffLib`) and cross-checked entry by entry
against pdf.js 3.11.174 (`CFFStandardStrings`, `StandardEncoding`, `ExpertEncoding`,
`ExpertCharset`, `ExpertSubsetCharset`); encodings are stored as code ↦ SID. -/


/-- The 391 predefined strings of CFF (TN #5176 Appendix A): SIDs 0–390. -/
def standardStrings : Array String := #[
  ".notdef", "space", "exclam", "quotedbl", "numbersign", "dollar", "percent", "ampersand",
  "quoteright", "parenleft", "parenright", "asterisk", "plus", "comma", "hyphen", "period",
  "slash", "zero", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine",
  "colon", "semicolon", "less", "equal", "greater", "question", "at", "A", "B", "C", "D", "E",
  "F", "G", "H", "I", "J", "K", "L", "M", "N", "O", "P", "Q", "R", "S", "T", "U", "V", "W", "X",
  "Y", "Z", "bracketleft", "backslash", "bracketright", "asciicircum", "underscore", "quoteleft",
  "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r", "s",
  "t", "u", "v", "w", "x", "y", "z", "braceleft", "bar", "braceright", "asciitilde",
  "exclamdown", "cent", "sterling", "fraction", "yen", "florin", "section", "currency",
  "quotesingle", "quotedblleft", "guillemotleft", "guilsinglleft", "guilsinglright", "fi", "fl",
  "endash", "dagger", "daggerdbl", "periodcentered", "paragraph", "bullet", "quotesinglbase",
  "quotedblbase", "quotedblright", "guillemotright", "ellipsis", "perthousand", "questiondown",
  "grave", "acute", "circumflex", "tilde", "macron", "breve", "dotaccent", "dieresis", "ring",
  "cedilla", "hungarumlaut", "ogonek", "caron", "emdash", "AE", "ordfeminine", "Lslash",
  "Oslash", "OE", "ordmasculine", "ae", "dotlessi", "lslash", "oslash", "oe", "germandbls",
  "onesuperior", "logicalnot", "mu", "trademark", "Eth", "onehalf", "plusminus", "Thorn",
  "onequarter", "divide", "brokenbar", "degree", "thorn", "threequarters", "twosuperior",
  "registered", "minus", "eth", "multiply", "threesuperior", "copyright", "Aacute",
  "Acircumflex", "Adieresis", "Agrave", "Aring", "Atilde", "Ccedilla", "Eacute", "Ecircumflex",
  "Edieresis", "Egrave", "Iacute", "Icircumflex", "Idieresis", "Igrave", "Ntilde", "Oacute",
  "Ocircumflex", "Odieresis", "Ograve", "Otilde", "Scaron", "Uacute", "Ucircumflex", "Udieresis",
  "Ugrave", "Yacute", "Ydieresis", "Zcaron", "aacute", "acircumflex", "adieresis", "agrave",
  "aring", "atilde", "ccedilla", "eacute", "ecircumflex", "edieresis", "egrave", "iacute",
  "icircumflex", "idieresis", "igrave", "ntilde", "oacute", "ocircumflex", "odieresis", "ograve",
  "otilde", "scaron", "uacute", "ucircumflex", "udieresis", "ugrave", "yacute", "ydieresis",
  "zcaron", "exclamsmall", "Hungarumlautsmall", "dollaroldstyle", "dollarsuperior",
  "ampersandsmall", "Acutesmall", "parenleftsuperior", "parenrightsuperior", "twodotenleader",
  "onedotenleader", "zerooldstyle", "oneoldstyle", "twooldstyle", "threeoldstyle",
  "fouroldstyle", "fiveoldstyle", "sixoldstyle", "sevenoldstyle", "eightoldstyle",
  "nineoldstyle", "commasuperior", "threequartersemdash", "periodsuperior", "questionsmall",
  "asuperior", "bsuperior", "centsuperior", "dsuperior", "esuperior", "isuperior", "lsuperior",
  "msuperior", "nsuperior", "osuperior", "rsuperior", "ssuperior", "tsuperior", "ff", "ffi",
  "ffl", "parenleftinferior", "parenrightinferior", "Circumflexsmall", "hyphensuperior",
  "Gravesmall", "Asmall", "Bsmall", "Csmall", "Dsmall", "Esmall", "Fsmall", "Gsmall", "Hsmall",
  "Ismall", "Jsmall", "Ksmall", "Lsmall", "Msmall", "Nsmall", "Osmall", "Psmall", "Qsmall",
  "Rsmall", "Ssmall", "Tsmall", "Usmall", "Vsmall", "Wsmall", "Xsmall", "Ysmall", "Zsmall",
  "colonmonetary", "onefitted", "rupiah", "Tildesmall", "exclamdownsmall", "centoldstyle",
  "Lslashsmall", "Scaronsmall", "Zcaronsmall", "Dieresissmall", "Brevesmall", "Caronsmall",
  "Dotaccentsmall", "Macronsmall", "figuredash", "hypheninferior", "Ogoneksmall", "Ringsmall",
  "Cedillasmall", "questiondownsmall", "oneeighth", "threeeighths", "fiveeighths",
  "seveneighths", "onethird", "twothirds", "zerosuperior", "foursuperior", "fivesuperior",
  "sixsuperior", "sevensuperior", "eightsuperior", "ninesuperior", "zeroinferior", "oneinferior",
  "twoinferior", "threeinferior", "fourinferior", "fiveinferior", "sixinferior", "seveninferior",
  "eightinferior", "nineinferior", "centinferior", "dollarinferior", "periodinferior",
  "commainferior", "Agravesmall", "Aacutesmall", "Acircumflexsmall", "Atildesmall",
  "Adieresissmall", "Aringsmall", "AEsmall", "Ccedillasmall", "Egravesmall", "Eacutesmall",
  "Ecircumflexsmall", "Edieresissmall", "Igravesmall", "Iacutesmall", "Icircumflexsmall",
  "Idieresissmall", "Ethsmall", "Ntildesmall", "Ogravesmall", "Oacutesmall", "Ocircumflexsmall",
  "Otildesmall", "Odieresissmall", "OEsmall", "Oslashsmall", "Ugravesmall", "Uacutesmall",
  "Ucircumflexsmall", "Udieresissmall", "Yacutesmall", "Thornsmall", "Ydieresissmall", "001.000",
  "001.001", "001.002", "001.003", "Black", "Bold", "Book", "Light", "Medium", "Regular",
  "Roman", "Semibold"]

/-- The predefined Standard Encoding (TN #5176 Appendix B): code ↦ SID (0 = `.notdef`). -/
def standardEncodingSids : Array Nat := #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26,
  27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50,
  51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74,
  75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 96,
  97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 0, 111, 112, 113, 114, 0,
  115, 116, 117, 118, 119, 120, 121, 122, 0, 123, 0, 124, 125, 126, 127, 128, 129, 130, 131, 0,
  132, 133, 0, 134, 135, 136, 137, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 138, 0, 139,
  0, 0, 0, 0, 140, 141, 142, 143, 0, 0, 0, 0, 0, 144, 0, 0, 0, 145, 0, 0, 146, 147, 148, 149, 0,
  0, 0, 0]

/-- The predefined Expert Encoding (TN #5176 Appendix B): code ↦ SID (0 = `.notdef`). -/
def expertEncodingSids : Array Nat := #[
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  1, 229, 230, 0, 231, 232, 233, 234, 235, 236, 237, 238, 13, 14, 15, 99, 239, 240, 241, 242,
  243, 244, 245, 246, 247, 248, 27, 28, 249, 250, 251, 252, 0, 253, 254, 255, 256, 257, 0, 0, 0,
  258, 0, 0, 259, 260, 261, 262, 0, 0, 263, 264, 265, 0, 266, 109, 110, 267, 268, 269, 0, 270,
  271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289,
  290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 304, 305, 306, 0,
  0, 307, 308, 309, 310, 311, 0, 312, 0, 0, 313, 0, 0, 314, 315, 0, 0, 316, 317, 318, 0, 0, 0,
  158, 155, 163, 319, 320, 321, 322, 323, 324, 325, 0, 0, 326, 150, 164, 169, 327, 328, 329, 330,
  331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349,
  350, 351, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 368,
  369, 370, 371, 372, 373, 374, 375, 376, 377, 378]

/-- The predefined Expert charset (TN #5176 Appendix C): GID ↦ SID. -/
def expertCharsetSids : Array Nat := #[
  0, 1, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 13, 14, 15, 99, 239, 240, 241, 242,
  243, 244, 245, 246, 247, 248, 27, 28, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259,
  260, 261, 262, 263, 264, 265, 266, 109, 110, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276,
  277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295,
  296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314,
  315, 316, 317, 318, 158, 155, 163, 319, 320, 321, 322, 323, 324, 325, 326, 150, 164, 169, 327,
  328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346,
  347, 348, 349, 350, 351, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365,
  366, 367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378]

/-- The predefined ExpertSubset charset (TN #5176 Appendix C): GID ↦ SID. -/
def expertSubsetCharsetSids : Array Nat := #[
  0, 1, 231, 232, 235, 236, 237, 238, 13, 14, 15, 99, 239, 240, 241, 242, 243, 244, 245, 246,
  247, 248, 27, 28, 249, 250, 251, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264,
  265, 266, 109, 110, 267, 268, 269, 270, 272, 300, 301, 302, 305, 314, 315, 158, 155, 163, 320,
  321, 322, 323, 324, 325, 326, 150, 164, 169, 327, 328, 329, 330, 331, 332, 333, 334, 335, 336,
  337, 338, 339, 340, 341, 342, 343, 344, 345, 346]


/-! ## Charsets (§13) -/

/-- Format-0 charset entries: `n` SIDs/CIDs of 2 bytes from `pos`, appended to `acc`. -/
def charset0 (b : ByteArray) : Nat → Nat → Array Nat → Except String (Array Nat)
  | _, 0, acc => .ok acc
  | pos, n + 1, acc =>
    match u16 b pos with
    | some v => charset0 b (pos + 2) n (acc.push v)
    | none => .error "truncated charset"

/-- Format-1/2 charset ranges from `pos` (`wide`: 2-byte `nLeft`), until `need` more glyphs are
covered. Each range covers at least one glyph, so `need` steps of fuel suffice. -/
def charsetRanges (b : ByteArray) (wide : Bool) : Nat → Nat → Nat → Array Nat →
    Except String (Array Nat)
  | 0, _, need, acc => if need = 0 then .ok acc else .error "charset ranges run out of fuel"
  | fuel + 1, pos, need, acc =>
    if need = 0 then .ok acc
    else
      match u16 b pos, (if wide then u16 b (pos + 2) else u8 b (pos + 2)) with
      | some first, some nLeft =>
        let k := min (nLeft + 1) need
        charsetRanges b wide fuel (pos + (if wide then 4 else 3)) (need - k)
          (acc ++ (Array.range k).map (first + ·))
      | _, _ => .error "truncated charset range"

/-- The charset at offset `off` (§13): GID ↦ SID (or CID). Offsets 0, 1, 2 are the predefined
ISOAdobe, Expert and ExpertSubset charsets; for a CID-keyed font (`cid`) they mean the
identity. GID 0 is always `.notdef` (SID/CID 0). -/
def parseCharset (b : ByteArray) (off nGlyphs : Nat) (cid : Bool) : Except String (Array Nat) :=
  if off ≤ 2 then
    .ok <| Array.ofFn (n := nGlyphs) fun i =>
      if cid then i.val
      else if off == 0 then (if i.val < 229 then i.val else 0)
      else if off == 1 then expertCharsetSids.getD i.val 0
      else expertSubsetCharsetSids.getD i.val 0
  else
    match u8 b off with
    | none => .error "truncated charset"
    | some 0 => charset0 b (off + 1) (nGlyphs - 1) #[0]
    | some 1 => charsetRanges b false nGlyphs (off + 1) (nGlyphs - 1) #[0]
    | some 2 => charsetRanges b true nGlyphs (off + 1) (nGlyphs - 1) #[0]
    | some f => .error s!"unknown charset format {f}"

/-- The inverse of a GID ↦ SID/CID table: SID/CID ↦ the first GID with it (at most 65536
entries). -/
def invert (xs : Array Nat) : Array (Option Nat) :=
  let n := min (xs.foldl max 0 + 1) 65536
  (xs.zipIdx).foldl (fun a (v, g) =>
    match a[v]? with
    | some none => a.setIfInBounds v (some g)
    | _ => a) (Array.replicate n none)

/-! ## Encodings (§12) -/

/-- A predefined encoding (code ↦ SID) through the charset inverse: code ↦ GID. -/
def predefEncoding (sids : Array Nat) (inv : Array (Option Nat)) : Array (Option Nat) :=
  Array.ofFn (n := 256) fun c =>
    match sids[c.val]? with
    | some 0 | none => none
    | some sid => (inv[sid]?).join

/-- Format-0 encoding: `n` codes from `pos`, code `k` for GID `gid` onwards. -/
def enc0 (b : ByteArray) :
    Nat → Nat → Nat → Array (Option Nat) → Except String (Array (Option Nat))
  | _, _, 0, e => .ok e
  | pos, gid, n + 1, e =>
    match u8 b pos with
    | some c => enc0 b (pos + 1) (gid + 1) n (e.setIfInBounds c (some gid))
    | none => .error "truncated encoding"

/-- Codes `c, c+1, …` (`n` of them) for consecutive GIDs from `gid`. -/
def encRange (c gid : Nat) : Nat → Array (Option Nat) → Array (Option Nat)
  | 0, e => e
  | n + 1, e => encRange (c + 1) (gid + 1) n (e.setIfInBounds c (some gid))

/-- Format-1 encoding: `n` ranges `(first, nLeft)` from `pos`, GIDs from `gid` on. -/
def enc1 (b : ByteArray) :
    Nat → Nat → Nat → Array (Option Nat) → Except String (Array (Option Nat))
  | _, _, 0, e => .ok e
  | pos, gid, n + 1, e =>
    match u8 b pos, u8 b (pos + 1) with
    | some first, some nLeft =>
      enc1 b (pos + 2) (gid + nLeft + 1) n (encRange first gid (nLeft + 1) e)
    | _, _ => .error "truncated encoding range"

/-- Encoding supplements: `n` pairs `(code, SID)` from `pos`, mapped through the inverse
charset. -/
def encSups (b : ByteArray) (inv : Array (Option Nat)) :
    Nat → Nat → Array (Option Nat) → Except String (Array (Option Nat))
  | _, 0, e => .ok e
  | pos, n + 1, e =>
    match u8 b pos, u16 b (pos + 1) with
    | some c, some sid =>
      encSups b inv (pos + 3) n (match (inv[sid]?).join with
        | some g => e.setIfInBounds c (some g)
        | none => e)
    | _, _ => .error "truncated encoding supplement"

/-- The encoding at offset `off` (§12): code ↦ GID. GIDs not below `nGlyphs` are dropped. -/
def parseEncoding (b : ByteArray) (off nGlyphs : Nat) (inv : Array (Option Nat)) :
    Except String (Array (Option Nat)) := do
  let e ← if off == 0 then pure (predefEncoding standardEncodingSids inv)
    else if off == 1 then pure (predefEncoding expertEncodingSids inv)
    else
      match u8 b off, u8 b (off + 1) with
      | some fmt, some n =>
        let base : Array (Option Nat) := Array.replicate 256 none
        let (e1, supPos) ← match fmt % 128 with
          | 0 => do pure (← enc0 b (off + 2) 1 n base, off + 2 + n)
          | 1 => do pure (← enc1 b (off + 2) 1 n base, off + 2 + 2 * n)
          | f => throw s!"unknown encoding format {f}"
        if fmt ≥ 128 then
          match u8 b supPos with
          | some ns => encSups b inv (supPos + 1) ns e1
          | none => throw "truncated encoding supplements"
        else pure e1
      | _, _ => throw "truncated encoding"
  pure (e.map fun g => g.bind fun g => if g < nGlyphs then some g else none)

/-- An encoding as a 256-entry array (`parseEncoding` always returns 256 entries; anything else
would become the empty encoding), so the font can carry `CFFFont.encoding_size`. -/
def fixEncoding (e : Array (Option Nat)) : {a : Array (Option Nat) // a.size = 256} :=
  if h : e.size = 256 then ⟨e, h⟩ else ⟨Array.replicate 256 none, Array.size_replicate⟩

/-! ## FDSelect (§19) -/

/-- Set entries `start, start+1, …` (`n` of them) of `a` to `v`. -/
def fill (v : Nat) : Array Nat → Nat → Nat → Array Nat
  | a, _, 0 => a
  | a, start, n + 1 => fill v (a.setIfInBounds start v) (start + 1) n

/-- Format-3 FDSelect ranges from `pos` (`n` of them, then the sentinel); `prev` is the first
GID of the previous range (ranges must start at 0 and strictly increase). -/
def fdRanges (b : ByteArray) (nGlyphs : Nat) :
    Nat → Nat → Option Nat → Array Nat → Except String (Array Nat)
  | _, 0, _, a => .ok a
  | pos, n + 1, prev, a =>
    match u16 b pos, u8 b (pos + 2), u16 b (pos + 3) with
    | some first, some fd, some next =>
      let okStart := match prev with
        | none => first == 0
        | some p => p < first
      if okStart && first < next then
        let stop := min next nGlyphs
        fdRanges b nGlyphs (pos + 3) n (some first) (fill fd a first (stop - first))
      else .error "FDSelect ranges not increasing"
    | _, _, _ => .error "truncated FDSelect"

/-- The FDSelect at offset `off`: GID ↦ Font DICT index. -/
def parseFDSelect (b : ByteArray) (off nGlyphs : Nat) : Except String (Array Nat) :=
  match u8 b off with
  | some 0 =>
    if off + 1 + nGlyphs ≤ b.size then
      .ok ((b.extract (off + 1) (off + 1 + nGlyphs)).toList.toArray.map (·.toNat))
    else .error "truncated FDSelect"
  | some 3 =>
    match u16 b (off + 1) with
    | some n => fdRanges b nGlyphs (off + 3) n none (Array.replicate nGlyphs 0)
    | none => .error "truncated FDSelect"
  | some f => .error s!"unknown FDSelect format {f}"
  | none => .error "truncated FDSelect"

/-! ## Private DICT (§15) -/

/-- What the interpreter needs from a Private DICT. -/
structure PrivInfo where
  /-- `defaultWidthX` (20). -/
  defaultW : Fixed := Fixed.zero
  /-- `nominalWidthX` (21). -/
  nominalW : Fixed := Fixed.zero
  /-- Local subroutines (`Subrs`, 19). -/
  subrs : Array ByteArray := #[]

/-- A single numeric operand of key `k` as `Fixed` (0 when absent). -/
def dictFixed (es : List DictEntry) (k : Nat) : Except String Fixed :=
  match dictGet es k with
  | none => .ok Fixed.zero
  | some [x] => .ok (Fixed.ofDecimal x)
  | some _ => .error s!"DICT operator {k}: expected one operand"

/-- The Private DICT named by the `Private` (18) entry of `es` (a Top or Font DICT), with its
local subroutines (at most `maxSubrs` of them, else `Error.limitExceeded .fontSubrs`). A DICT
without `Private` gets zero widths and no subroutines. -/
def parsePrivate (maxSubrs : Nat) (b : ByteArray) (es : List DictEntry) : Except Error PrivInfo :=
  match dictGet es 18 with
  | none => .ok {}
  | some [sz, off] =>
    match decToNat? sz, decToNat? off with
    | some size, some off =>
      if off + size ≤ b.size then do
        let pes ← liftE (parseDict (b.extract off (off + size)) 0 [] [])
        let defaultW ← liftE (dictFixed pes 20)
        let nominalW ← liftE (dictFixed pes 21)
        let subrs ← match dictGet pes 19 with
          | none => pure #[]
          | some [o] => match decToNat? o with
            | some o => do
              let ⟨ix, _⟩ ← limitIndex b (off + o) maxSubrs .fontSubrs
              pure (ix.items b)
            | none => liftE (.error "bad Subrs offset")
          | some _ => liftE (.error "bad Subrs operand")
        pure { defaultW, nominalW, subrs }
      else liftE (.error "Private DICT out of bounds")
    | _, _ => liftE (.error "bad Private operands")
  | some _ => liftE (.error "bad Private operands")

/-! ## Type 2 charstring interpreter (TN #5177) -/

/-- An operand stack bounded by `maxStack` by construction (top first). -/
abbrev Stack := {l : List Fixed // l.length ≤ maxStack}

/-- The empty stack. -/
def Stack.empty : Stack := ⟨[], Nat.zero_le _⟩

/-- Push, failing on overflow. -/
def Stack.push (s : Stack) (x : Fixed) : Except String Stack :=
  if h : s.1.length < maxStack then .ok ⟨x :: s.1, by simp only [List.length_cons]; omega⟩
  else .error "charstring stack overflow"

/-- Pop the top, failing on underflow. -/
def Stack.pop : Stack → Except String (Fixed × Stack)
  | ⟨x :: r, h⟩ => .ok (x, ⟨r, by simp only [List.length_cons] at h; omega⟩)
  | ⟨[], _⟩ => .error "charstring stack underflow"

/-- A return address: the calling charstring and the position after the call. -/
structure Frame where
  /-- The calling charstring. -/
  code : ByteArray
  /-- The position to resume at. -/
  pos : Nat

/-- The interpreter state. Stack and call depth are bounded by their types. -/
structure CState where
  /-- The argument stack. -/
  stack : Stack := Stack.empty
  /-- The subroutine return stack, at most `maxCallDepth` deep. -/
  calls : {l : List Frame // l.length ≤ maxCallDepth} := ⟨[], Nat.zero_le _⟩
  /-- Stem hints declared so far (for the hint-mask length). -/
  nStems : Nat := 0
  /-- The first stack-clearing operator has been seen (the width can no longer appear). -/
  widthDone : Bool := false
  /-- The explicit width operand (relative to `nominalWidthX`), if any. -/
  width : Option Fixed := none
  /-- The `endchar` accent form's `(base code, accent code)`, if used. -/
  seac : Option (UInt8 × UInt8) := none
  /-- Record path operators (task 7.3a; `false` for metrics, which then only clear). -/
  record : Bool := false
  /-- The recorded path (when `record`). -/
  path : Outline.PathAcc := {}
  /-- The `endchar` accent offset `(adx, ady)`, if used. -/
  seacArgs : Option (Fixed × Fixed) := none

/-! ### Path recording (task 7.3a; TN #5177 §4.1) -/

/-- Lines alternating horizontal and vertical (`hlineto`/`vlineto`). -/
def altLines (a : Outline.PathAcc) (horiz : Bool) : List Fixed → Except String Outline.PathAcc
  | [] => .ok a
  | d :: rest => do
    let a ← if horiz then a.rlineTo d Fixed.zero else a.rlineTo Fixed.zero d
    altLines a (!horiz) rest

/-- `{dx dy}+` lines (`rlineto`; a trailing odd operand is ignored). -/
def pairLines (a : Outline.PathAcc) : List Fixed → Except String Outline.PathAcc
  | dx :: dy :: rest => do
    let a ← a.rlineTo dx dy
    pairLines a rest
  | _ => .ok a

/-- `{dxa dya dxb dyb dxc dyc}+` curves (`rrcurveto`; leftover operands are ignored). -/
def sixCurves (a : Outline.PathAcc) : List Fixed → Except String Outline.PathAcc
  | x1 :: y1 :: x2 :: y2 :: x3 :: y3 :: rest => do
    let a ← a.rcurveTo x1 y1 x2 y2 x3 y3
    sixCurves a rest
  | _ => .ok a

/-- `hvcurveto`/`vhcurveto` curves, alternating the start tangent; a final fifth operand is
the end tangent's other coordinate. -/
def altCurves (a : Outline.PathAcc) (horiz : Bool) : List Fixed → Except String Outline.PathAcc
  | [p, q, r, s, t] =>
    if horiz then a.rcurveTo p Fixed.zero q r t s else a.rcurveTo Fixed.zero p q r s t
  | p :: q :: r :: s :: rest => do
    let a ← if horiz then a.rcurveTo p Fixed.zero q r Fixed.zero s
      else a.rcurveTo Fixed.zero p q r s Fixed.zero
    altCurves a (!horiz) rest
  | _ => .ok a

/-- `vvcurveto` (`horiz = false`) / `hhcurveto` (`true`) curves: groups of four, the first
optionally preceded by the other coordinate of its start tangent (`d1`). -/
def sameCurves (a : Outline.PathAcc) (horiz : Bool) (d1 : Fixed) :
    List Fixed → Except String Outline.PathAcc
  | p :: q :: r :: s :: rest => do
    let a ← if horiz then a.rcurveTo p d1 q r s Fixed.zero
      else a.rcurveTo d1 p q r Fixed.zero s
    sameCurves a horiz Fixed.zero rest
  | _ => .ok a

/-- The sum of a list of `Fixed` (saturating). -/
def fsum (l : List Fixed) : Fixed := l.foldl Fixed.add Fixed.zero

/-- The absolute value of a `Fixed`. -/
def fabs (x : Fixed) : Fixed := if x.raw < 0 then Fixed.neg x else x

/-- A Type 2 path operator `v` (one byte, or `1200 + w` for the flex escapes) on the operands
`xs` (bottom first). -/
def recordOp (a : Outline.PathAcc) (v : Nat) (xs : List Fixed) : Except String Outline.PathAcc :=
  let z := Fixed.zero
  let g (k : Nat) := xs.getD k z
  if v == 5 then pairLines a xs
  else if v == 6 then altLines a true xs
  else if v == 7 then altLines a false xs
  else if v == 8 then sixCurves a xs
  else if v == 24 then do
    -- rcurveline: curves, then a line
    let a ← sixCurves a (xs.take (xs.length - 2))
    a.rlineTo (g (xs.length - 2)) (g (xs.length - 1))
  else if v == 25 then do
    -- rlinecurve: lines, then a curve
    let a ← pairLines a (xs.take (xs.length - 6))
    let k := xs.length - 6
    a.rcurveTo (g k) (g (k + 1)) (g (k + 2)) (g (k + 3)) (g (k + 4)) (g (k + 5))
  else if v == 26 then
    if xs.length % 2 == 1 then sameCurves a false (g 0) (xs.drop 1) else sameCurves a false z xs
  else if v == 27 then
    if xs.length % 2 == 1 then sameCurves a true (g 0) (xs.drop 1) else sameCurves a true z xs
  else if v == 30 then altCurves a false xs
  else if v == 31 then altCurves a true xs
  else if v == 1235 then sixCurves a (xs.take 12)
  else if v == 1234 then do
    -- hflex: dx1 dx2 dy2 dx3 dx4 dx5 dx6
    let a ← a.rcurveTo (g 0) z (g 1) (g 2) (g 3) z
    a.rcurveTo (g 4) z (g 5) (Fixed.neg (g 2)) (g 6) z
  else if v == 1236 then do
    -- hflex1: dx1 dy1 dx2 dy2 dx3 dx4 dx5 dy5 dx6
    let a ← a.rcurveTo (g 0) (g 1) (g 2) (g 3) (g 4) z
    a.rcurveTo (g 5) z (g 6) (g 7) (g 8) (Fixed.neg (fsum [g 1, g 3, g 7]))
  else if v == 1237 then do
    -- flex1: dx1 dy1 … dx5 dy5 d6
    let dx := fsum [g 0, g 2, g 4, g 6, g 8]
    let dy := fsum [g 1, g 3, g 5, g 7, g 9]
    let a ← a.rcurveTo (g 0) (g 1) (g 2) (g 3) (g 4) (g 5)
    if (fabs dy).raw < (fabs dx).raw then a.rcurveTo (g 6) (g 7) (g 8) (g 9) (g 10) (Fixed.neg dy)
    else a.rcurveTo (g 6) (g 7) (g 8) (g 9) (Fixed.neg dx) (g 10)
  else .ok a

/-- Apply a path operator to the state when recording (operands: the whole stack, bottom
first, after the width operand `skip` if it is taken here). -/
def recordSt (st : CState) (v : Nat) (skip : Bool) : Except String CState :=
  if st.record then do
    let xs := st.stack.1.reverse
    let a ← recordOp st.path v (if skip then xs.drop 1 else xs)
    .ok { st with path := a }
  else .ok st

/-- A move while recording (`rmoveto` 21, `hmoveto` 22, `vmoveto` 4), after the width operand
`skip` if it is taken here. -/
def recordMove (st : CState) (v : Nat) (skip : Bool) : Except String CState :=
  if st.record then do
    let xs := st.stack.1.reverse
    let xs := if skip then xs.drop 1 else xs
    let z := Fixed.zero
    let a ← if v == 21 then st.path.rmoveTo (xs.getD 0 z) (xs.getD 1 z)
      else if v == 22 then st.path.rmoveTo (xs.getD 0 z) z
      else st.path.rmoveTo z (xs.getD 0 z)
    .ok { st with path := a }
  else .ok st

/-- The subroutine bias for a Subrs INDEX of `n` entries (TN #5177 §4.7). -/
def bias (n : Nat) : Int := if n < 1240 then 107 else if n < 33900 then 1131 else 32768

/-- The bias is positive. -/
theorem bias_pos (n : Nat) : 0 < bias n := by
  unfold bias; split
  · decide
  · split <;> decide

/-- Decode the charstring number starting with byte `v` (`28` or `≥ 32`) at `pos` (TN #5177
§3.2): the value and the position after it. -/
def decodeNum (code : ByteArray) (pos v : Nat) : Option (Fixed × Nat) :=
  if v == 28 then (u16 code (pos + 1)).map fun w => (Fixed.ofInt (toI16 w), pos + 3)
  else if v ≤ 246 then some (Fixed.ofInt ((v : Int) - 139), pos + 1)
  else if v ≤ 250 then
    (u8 code (pos + 1)).map fun w => (Fixed.ofInt ((v - 247) * 256 + w + 108 : Nat), pos + 2)
  else if v ≤ 254 then
    (u8 code (pos + 1)).map fun w =>
      (Fixed.ofInt (-(((v - 251) * 256 + w + 108 : Nat) : Int)), pos + 2)
  else
    (readBE code (pos + 1) 4 0).map fun w =>
      (Fixed.clamp (roundDiv (toI32 w * fixedScale) 65536), pos + 5)

/-- An integral `Fixed` as an `Int`. -/
def Fixed.toInt? (x : Fixed) : Option Int :=
  if x.raw % fixedScale = 0 then some (x.raw / fixedScale) else none

/-- A character code operand (integral, `0 … 255`). -/
def toCode? (x : Fixed) : Option UInt8 :=
  match Fixed.toInt? x with
  | some n => if 0 ≤ n ∧ n < 256 then some n.toNat.toUInt8 else none
  | none => none

/-- The boolean `1`/`0` as `Fixed`. -/
def ofBool (b : Bool) : Fixed := if b then Fixed.one else Fixed.zero

/-- Pop two operands `a b` (b on top) and push `f a b`. -/
def binOp (s : Stack) (f : Fixed → Fixed → Except String Fixed) : Except String Stack := do
  let (y, s1) ← s.pop
  let (x, s2) ← s1.pop
  s2.push (← f x y)

/-- Pop one operand and push `f` of it. -/
def unOp (s : Stack) (f : Fixed → Fixed) : Except String Stack := do
  let (x, s1) ← s.pop
  s1.push (f x)

/-- The arithmetic and stack escape operators `12 w` (TN #5177 §4.5) on the stack. -/
def arith (w : Nat) (s : Stack) : Except String Stack :=
  if w == 3 then binOp s fun a b => .ok (ofBool (a.raw != 0 && b.raw != 0))
  else if w == 4 then binOp s fun a b => .ok (ofBool (a.raw != 0 || b.raw != 0))
  else if w == 5 then unOp s fun a => ofBool (a.raw == 0)
  else if w == 9 then unOp s fun a => if a.raw < 0 then Fixed.neg a else a
  else if w == 10 then binOp s fun a b => .ok (Fixed.add a b)
  else if w == 11 then binOp s fun a b => .ok (Fixed.sub a b)
  else if w == 12 then
    binOp s fun a b =>
      if b.raw = 0 then .error "charstring division by zero" else .ok (Fixed.div a b)
  else if w == 14 then unOp s Fixed.neg
  else if w == 15 then binOp s fun a b => .ok (ofBool (a.raw == b.raw))
  else if w == 18 then do let (_, s1) ← s.pop; pure s1
  else if w == 24 then binOp s fun a b => .ok (Fixed.mul a b)
  else if w == 27 then do let (x, _) ← s.pop; s.push x
  else if w == 28 then do
    let (y, s1) ← s.pop
    let (x, s2) ← s1.pop
    let s3 ← s2.push y
    s3.push x
  else .error s!"unsupported charstring operator 12 {w}"

/-- Record the width operand at the first stack-clearing operator: `extra` says whether the
stack holds one operand more than the operator takes (it is then the bottom one). -/
def takeWidth (st : CState) (extra : Bool) : CState :=
  if st.widthDone then st
  else { st with widthDone := true, width := if extra then st.stack.1.getLast? else none }

/-- Lift a result with `r ≤ n` remaining fuel to `r ≤ n + 1`. -/
def up {α : Type} {n : Nat} :
    Except String (α × {r : Nat // r ≤ n}) → Except String (α × {r : Nat // r ≤ n + 1})
  | .ok (a, ⟨r, h⟩) => .ok (a, ⟨r, Nat.le_succ_of_le h⟩)
  | .error e => .error e

/-- Whether `v` is a path-construction operator (stack-clearing, no width). -/
def isPathOp (v : Nat) : Bool :=
  v == 5 || v == 6 || v == 7 || v == 8 || v == 24 || v == 25 || v == 26 || v == 27 ||
  v == 30 || v == 31

/-- Run a Type 2 charstring (TN #5177 §4) from `pos` with at most `fuel` steps, returning the
state at `endchar` and the fuel left (never more than given, by its type). `gsubrs`/`lsubrs`
are the global and local subroutines. -/
def run (gsubrs lsubrs : Array ByteArray) :
    (fuel : Nat) → ByteArray → Nat → CState →
      Except String (CState × {r : Nat // r ≤ fuel})
  | 0, _, _, _ => .error "charstring fuel exhausted"
  | fuel + 1, code, pos, st =>
    match code[pos]? with
    | none =>
      match st.calls with
      | ⟨f :: fs, h⟩ =>
        up (run gsubrs lsubrs fuel f.code f.pos
          { st with calls := ⟨fs, Nat.le_of_succ_le h⟩ })
      | ⟨[], _⟩ => .error "charstring ends without endchar"
    | some b =>
      let v := b.toNat
      let n := st.stack.1.length
      let clear (s : CState) : CState := { s with stack := Stack.empty }
      if v == 28 || 32 ≤ v then
        match decodeNum code pos v with
        | none => .error "truncated charstring number"
        | some (x, pos') => do
          let s ← st.stack.push x
          up (run gsubrs lsubrs fuel code pos' { st with stack := s })
      else if v == 1 || v == 3 || v == 18 || v == 23 then
        let st1 := takeWidth st (n % 2 == 1)
        up (run gsubrs lsubrs fuel code (pos + 1) (clear { st1 with nStems := st.nStems + n / 2 }))
      else if v == 19 || v == 20 then
        let st1 := takeWidth st (n % 2 == 1)
        let stems := st.nStems + n / 2
        let skip := (stems + 7) / 8
        if pos + 1 + skip ≤ code.size then
          up (run gsubrs lsubrs fuel code (pos + 1 + skip) (clear { st1 with nStems := stems }))
        else .error "truncated hint mask"
      else if v == 21 then do
        let st1 ← recordMove st v (2 < n && !st.widthDone)
        up (run gsubrs lsubrs fuel code (pos + 1) (clear (takeWidth st1 (2 < n))))
      else if v == 22 || v == 4 then do
        let st1 ← recordMove st v (1 < n && !st.widthDone)
        up (run gsubrs lsubrs fuel code (pos + 1) (clear (takeWidth st1 (1 < n))))
      else if v == 14 then
        let extra := n == 1 || n == 5
        let st1 := takeWidth st extra
        let m := if extra && !st.widthDone then n - 1 else n
        match (if st.record then st1.path.close else .ok st1.path) with
        | .error e => .error e
        | .ok path =>
        let st1 := { st1 with path := path }
        if 4 ≤ m then
          match toCode? (st.stack.1.getD 1 Fixed.zero), toCode? (st.stack.1.getD 0 Fixed.zero) with
          | some bc, some ac =>
            let sa := (st.stack.1.getD 3 Fixed.zero, st.stack.1.getD 2 Fixed.zero)
            .ok (clear { st1 with seac := some (bc, ac), seacArgs := some sa },
              ⟨fuel, Nat.le_succ _⟩)
          | _, _ => .error "endchar: bad accent character code"
        else .ok (clear st1, ⟨fuel, Nat.le_succ _⟩)
      else if v == 10 || v == 29 then do
        let (ix, s1) ← st.stack.pop
        let subrs := if v == 10 then lsubrs else gsubrs
        match Fixed.toInt? ix with
        | none => .error "callsubr: non-integral index"
        | some i =>
          let j := i + bias subrs.size
          match (if 0 ≤ j then subrs[j.toNat]? else none) with
          | none => .error "callsubr: bad subroutine index"
          | some sub =>
            if h : st.calls.1.length < maxCallDepth then
              up (run gsubrs lsubrs fuel sub 0
                { st with stack := s1, calls := ⟨⟨code, pos + 1⟩ :: st.calls.1, h⟩ })
            else .error "callsubr: subroutines nested too deep"
      else if v == 11 then
        match st.calls with
        | ⟨f :: fs, h⟩ =>
          up (run gsubrs lsubrs fuel f.code f.pos
            { st with calls := ⟨fs, Nat.le_of_succ_le h⟩ })
        | ⟨[], _⟩ => .error "return outside a subroutine"
      else if isPathOp v then do
        let st1 ← recordSt st v false
        up (run gsubrs lsubrs fuel code (pos + 1) (clear { st1 with widthDone := true }))
      else if v == 12 then
        match u8 code (pos + 1) with
        | none => .error "truncated escape operator"
        | some w =>
          if w == 0 || (34 ≤ w ∧ w ≤ 37) then do
            let st1 ← recordSt st (1200 + w) false
            up (run gsubrs lsubrs fuel code (pos + 2) (clear { st1 with widthDone := true }))
          else
            match arith w st.stack with
            | .ok s => up (run gsubrs lsubrs fuel code (pos + 2) { st with stack := s })
            | .error e => .error e
      else .error s!"reserved charstring operator {v}"

/-- The argument stack of any state `run` returns holds at most `maxStack` operands (by
construction: `Stack` carries the bound). -/
theorem run_stack_le {g l : Array ByteArray} {fuel : Nat} {code : ByteArray} {pos : Nat}
    {st : CState} {r : CState × {r : Nat // r ≤ fuel}} (_h : run g l fuel code pos st = .ok r) :
    r.1.stack.1.length ≤ maxStack := r.1.stack.2

/-- Subroutine nesting in any state `run` reaches is at most `maxCallDepth` (by construction). -/
theorem run_calls_le {g l : Array ByteArray} {fuel : Nat} {code : ByteArray} {pos : Nat}
    {st : CState} {r : CState × {r : Nat // r ≤ fuel}} (_h : run g l fuel code pos st = .ok r) :
    r.1.calls.1.length ≤ maxCallDepth := r.1.calls.2

/-- **Step bound**: the fuel `run` reports left never exceeds the fuel it was given, so the
steps it used are `fuel - left` (by construction: every recursive call goes through `up`). -/
theorem run_steps_le {g l : Array ByteArray} {fuel : Nat} {code : ByteArray} {pos : Nat}
    {st : CState} {r : CState × {r : Nat // r ≤ fuel}} (_h : run g l fuel code pos st = .ok r) :
    r.2.1 ≤ fuel := r.2.2

/-- A glyph's metrics in glyph space. -/
structure Glyph where
  /-- Advance width (`nominalWidthX` + operand, or `defaultWidthX`). -/
  width : Fixed
  /-- The `endchar` accent form `(base code, accent code)`, if used. -/
  seac : Option (UInt8 × UInt8)
  deriving Repr, Inhabited

/-- Run one charstring with `fuel` steps under a Private DICT: the glyph and the steps used. -/
def evalGlyph (gsubrs : Array ByteArray) (priv : PrivInfo) (fuel : Nat) (code : ByteArray) :
    Except String (Glyph × Nat) :=
  match run gsubrs priv.subrs fuel code 0 {} with
  | .ok (st, ⟨left, _⟩) =>
    let w := match st.width with
      | some x => Fixed.add priv.nominalW x
      | none => priv.defaultW
    .ok ({ width := w, seac := st.seac }, fuel - left)
  | .error e => .error e

/-- Evaluate the charstrings `(gid, code)` in order with a remaining font-wide `budget` of
steps (initially `Limits.fontFuel`); each glyph gets `min glyphFuel budget` steps
(`Limits.glyphFuel`) and is charged what it used (all of it on failure). Pushes one entry per
charstring. -/
def evalList (glyphFuel : Nat) (gsubrs : Array ByteArray) (privs : Array PrivInfo)
    (fdOf : Nat → Nat) :
    List (Nat × ByteArray) → Nat → Array (Option Glyph) → Array (Nat × String) →
    Array (Option Glyph) × Array (Nat × String)
  | [], _, gs, rs => (gs, rs)
  | (gid, code) :: rest, budget, gs, rs =>
    match privs[fdOf gid]? with
    | none => evalList glyphFuel gsubrs privs fdOf rest budget (gs.push none)
        (rs.push (gid, "FDSelect names a missing Font DICT"))
    | some priv =>
      let fuel := min glyphFuel budget
      if fuel = 0 then
        evalList glyphFuel gsubrs privs fdOf rest budget (gs.push none)
          (rs.push (gid, "font charstring budget exhausted"))
      else
        match evalGlyph gsubrs priv fuel code with
        | .ok (g, used) =>
          evalList glyphFuel gsubrs privs fdOf rest (budget - used) (gs.push (some g)) rs
        | .error e => evalList glyphFuel gsubrs privs fdOf rest (budget - fuel) (gs.push none)
            (rs.push (gid, e))

/-- `evalList` pushes exactly one glyph entry per charstring. -/
theorem evalList_size (glyphFuel : Nat) (gsubrs : Array ByteArray) (privs : Array PrivInfo)
    (fdOf : Nat → Nat) :
    ∀ (l : List (Nat × ByteArray)) (budget : Nat) (gs : Array (Option Glyph))
      (rs : Array (Nat × String)),
      (evalList glyphFuel gsubrs privs fdOf l budget gs rs).1.size = gs.size + l.length := by
  intro l
  induction l with
  | nil => intro _ _ _; simp [evalList]
  | cons hd tl ih =>
    intro budget gs rs
    obtain ⟨gid, code⟩ := hd
    simp only [evalList]
    split
    · rw [ih]; simp only [Array.size_push, List.length_cons]; omega
    · split
      · rw [ih]; simp only [Array.size_push, List.length_cons]; omega
      · split
        · rw [ih]; simp only [Array.size_push, List.length_cons]; omega
        · rw [ih]; simp only [Array.size_push, List.length_cons]; omega

/-! ## The font -/

/-- A font bounding box in glyph space. -/
structure BBox where
  /-- Lower-left x. -/
  llx : Fixed
  /-- Lower-left y. -/
  lly : Fixed
  /-- Upper-right x. -/
  urx : Fixed
  /-- Upper-right y. -/
  ury : Fixed
  deriving Repr, Inhabited

/-- The text-space x-advance of a glyph of glyph-space width `w` under a font matrix whose `a`
entry is `a` (exact decimal): `w·a`, computed exactly and rounded once. -/
def textAdvance (a : Decimal) (w : Fixed) : Fixed :=
  Fixed.clamp (roundDiv (w.raw * a.mantissa) ((10 ^ a.scale : Nat) : Int))

/-- A parsed CFF font: what text extraction and glyph positioning need. -/
structure CFFFont where
  /-- The font name (first entry of the Name INDEX). -/
  name : String
  /-- Whether the font is CID-keyed (`ROS` present). -/
  isCID : Bool
  /-- `ROS`: registry, ordering, supplement (CID-keyed fonts). -/
  ros : Option (String × String × Nat)
  /-- The Top DICT `FontMatrix` (default `[0.001 0 0 0.001 0 0]`). -/
  fontMatrix : Matrix
  /-- The exact `a` entry of the effective font matrix of name-keyed fonts. -/
  matrixA : Decimal
  /-- `FontBBox` (zeros if absent). -/
  bbox : BBox
  /-- Number of glyphs (CharStrings INDEX count). -/
  numGlyphs : Nat
  /-- The glyph cap the font was parsed under (`Limits.maxCFFGlyphs`). -/
  maxGlyphs : Nat
  /-- The glyph count respects `maxGlyphs`. -/
  numGlyphs_le : numGlyphs ≤ maxGlyphs
  /-- The charset: GID ↦ SID (name-keyed) or CID (CID-keyed). -/
  charset : Array Nat
  /-- The inverse charset: SID/CID ↦ first GID. -/
  inverse : Array (Option Nat)
  /-- The String INDEX (SIDs `391 …`). -/
  strings : Array String
  /-- The encoding: code ↦ GID (all `none` for CID-keyed fonts). -/
  encoding : Array (Option Nat)
  /-- The encoding has 256 entries. -/
  encoding_size : encoding.size = 256
  /-- FDSelect: GID ↦ Font DICT (empty for name-keyed fonts). -/
  fdSelect : Array Nat
  /-- The exact `a` entry of each Font DICT's effective font matrix (CID-keyed fonts). -/
  fdMatrixA : Array Decimal
  /-- Validated glyphs by GID (`none` = rejected). -/
  glyphs : Array (Option Glyph)
  /-- One entry per glyph. -/
  glyphs_size : glyphs.size = numGlyphs
  /-- Rejected glyphs (GID) with the reason. -/
  rejected : Array (Nat × String)
  /-- The charstrings by GID (for outlines, task 7.3a). -/
  charstrings : Array ByteArray := #[]
  /-- The Global Subrs (for outlines). -/
  gsubrs : Array ByteArray := #[]
  /-- The Private DICTs (one per Font DICT; one for name-keyed fonts), for outlines. -/
  privs : Array PrivInfo := #[]

/-- The string of a SID: a standard string or an entry of the String INDEX. -/
def CFFFont.sidString? (f : CFFFont) (sid : Nat) : Option String :=
  if sid < nStdStrings then standardStrings[sid]? else f.strings[sid - nStdStrings]?

/-- The glyph name of a GID (name-keyed fonts only). -/
def CFFFont.glyphName? (f : CFFFont) (gid : Nat) : Option String :=
  if f.isCID then none else (f.charset[gid]?).bind f.sidString?

/-- The GID of a glyph name (name-keyed fonts only; first match). -/
def CFFFont.gidOfName? (f : CFFFont) (n : String) : Option Nat :=
  if f.isCID then none else f.charset.findIdx? fun sid => f.sidString? sid == some n

/-- The GID a character code selects through the font's encoding (simple fonts). -/
def CFFFont.gidOfCode (f : CFFFont) (code : UInt8) : Option Nat := (f.encoding[code.toNat]?).join

/-- The glyph name a character code selects (for mapping through the AGL). -/
def CFFFont.glyphNameOfCode (f : CFFFont) (code : UInt8) : Option String :=
  (f.gidOfCode code).bind f.glyphName?

/-- The GID of a CID: through the charset for CID-keyed fonts; for a name-keyed font used as a
CIDFont, CIDs are GIDs (ISO 32000-2 §9.7.4.2). -/
def CFFFont.gidOfCID (f : CFFFont) (cid : Nat) : Option Nat :=
  if f.isCID then (f.inverse[cid]?).join
  else if cid < f.numGlyphs then some cid else none

/-- The validated glyph with a GID. -/
def CFFFont.glyph? (f : CFFFont) (gid : Nat) : Option Glyph := (f.glyphs[gid]?).join

/-- The glyph-space advance width of a GID. -/
def CFFFont.widthOfGid (f : CFFFont) (gid : Nat) : Option Fixed := (f.glyph? gid).map (·.width)

/-- The exact `a` entry of the font matrix that applies to a GID. -/
def CFFFont.matrixAOf (f : CFFFont) (gid : Nat) : Decimal :=
  if f.isCID then f.fdMatrixA.getD (f.fdSelect.getD gid 0) f.matrixA else f.matrixA

/-- The text-space advance of a GID. -/
def CFFFont.advanceOfGid (f : CFFFont) (gid : Nat) : Option Fixed :=
  (f.widthOfGid gid).map (textAdvance (f.matrixAOf gid))

/-- The text-space advance of a character code through the encoding (simple fonts). -/
def CFFFont.advance (f : CFFFont) (code : UInt8) : Option Fixed :=
  (f.gidOfCode code).bind f.advanceOfGid

/-- The text-space advance of a CID (CIDFonts). -/
def CFFFont.advanceOfCID (f : CFFFont) (cid : Nat) : Option Fixed :=
  (f.gidOfCID cid).bind f.advanceOfGid

/-- **Advance law**: the advance of a code is the width of the glyph its encoding selects,
scaled by the font matrix's `a` entry and rounded once. -/
theorem CFFFont.advance_eq (f : CFFFont) (code : UInt8) :
    f.advance code = (f.gidOfCode code).bind fun g =>
      (f.glyph? g).map fun gl => textAdvance (f.matrixAOf g) gl.width := by
  unfold CFFFont.advance CFFFont.advanceOfGid CFFFont.widthOfGid
  cases f.gidOfCode code with
  | none => rfl
  | some g => simp only [Option.bind_some, Option.map_map]; rfl

/-- **Glyph-count cap** of a parsed font. -/
theorem CFFFont.numGlyphs_le_max (f : CFFFont) : f.numGlyphs ≤ f.maxGlyphs := f.numGlyphs_le

/-- The `a` entry of the composition of a Font DICT matrix `fd` with the Top DICT matrix
`top` (glyph space → FD matrix → top matrix): `fd.a·top.a + fd.b·top.c`. -/
def composeA (fd top : List Decimal) : Decimal :=
  let z : Decimal := ⟨0, 0⟩
  decAdd (decMul (fd.getD 0 z) (top.getD 0 z)) (decMul (fd.getD 1 z) (top.getD 2 z))

/-- Parse an embedded CFF font program (`/FontFile3` with `/Subtype /Type1C` or
`/CIDFontType0C`, Flate already decoded). Fails only when the structure is broken (header,
INDEXes, DICTs, charset, encoding, FDSelect; `malformed`), a limit is exceeded
(`limitExceeded`: `.decodedStreamBytes`, `.fontGlyphs` for more than `limits.maxCFFGlyphs`
charstrings, `.fontSubrs` for a Subrs INDEX of more than `limits.maxFontSubrs` entries,
`.fontDicts` for more than `limits.maxFontDicts` Font DICTs), or no glyph is valid; individual
bad charstrings are listed in `rejected` (including those left when `limits.fontFuel` is
spent). -/
def parse (limits : Limits) (bytes : ByteArray) : Except Error CFFFont := do
  if limits.maxDecodedStreamBytes < bytes.size then throw (.limitExceeded .decodedStreamBytes)
  let b := bytes
  let some major := u8 b 0 | throw (.malformed 0 "CFF: truncated header")
  if major == 2 then throw (.unsupported "CFF2 font program")
  if major != 1 then throw (.malformed 0 s!"CFF: unknown major version {major}")
  let some hdrSize := u8 b 2 | throw (.malformed 0 "CFF: truncated header")
  let ⟨nameIx, _⟩ ← liftE (parseIndex b hdrSize maxStrings)
  let ⟨topIx, _⟩ ← liftE (parseIndex b nameIx.endPos maxStrings)
  let ⟨strIx, _⟩ ← liftE (parseIndex b topIx.endPos maxStrings)
  let ⟨gsubrIx, _⟩ ← limitIndex b strIx.endPos limits.maxFontSubrs .fontSubrs
  let some name := nameIx.item b 0 | throw (.malformed 0 "CFF: empty Name INDEX")
  let some topData := topIx.item b 0 | throw (.malformed 0 "CFF: empty Top DICT INDEX")
  let top ← liftE (parseDict topData 0 [] [])
  let strings := (strIx.items b).map latin1
  let gsubrs := gsubrIx.items b
  let csType ← liftE (dictNat top 1206 2)
  if csType != 2 then throw (.unsupported s!"CFF CharstringType {csType}")
  let some [csOffD] := dictGet top 17 | throw (.malformed 0 "CFF: no CharStrings")
  let some csOff := decToNat? csOffD | throw (.malformed 0 "CFF: bad CharStrings offset")
  let ⟨csIx, csValid⟩ ← limitIndex b csOff limits.maxCFFGlyphs .fontGlyphs
  let nGlyphs := csIx.count
  if nGlyphs = 0 then throw (.malformed 0 "CFF: no glyphs")
  let rosOps := dictGet top 1230
  let isCID := rosOps.isSome
  let sidStr (sid : Nat) : String :=
    if sid < nStdStrings then standardStrings.getD sid "" else strings.getD (sid - nStdStrings) ""
  let ros : Option (String × String × Nat) := rosOps.bind fun
    | [r, o, s] => match decToNat? r, decToNat? o, decToNat? s with
      | some r, some o, some s => some (sidStr r, sidStr o, s)
      | _, _, _ => none
    | _ => none
  let charsetOff ← liftE (dictNat top 15 0)
  let charset ← liftE (parseCharset b charsetOff nGlyphs isCID)
  let inverse := invert charset
  let encOff ← liftE (dictNat top 16 0)
  let encoding ← if isCID then pure (Array.replicate 256 none)
    else liftE (parseEncoding b encOff nGlyphs inverse)
  let topM ← liftE (dictMatrix? top)
  let dm := topM.getD defaultMatrix
  let z : Decimal := ⟨0, 0⟩
  let (privs, fdSelect, fdMatrixA) ← if isCID then do
      let some [fdaD] := dictGet top 1236 | throw (.malformed 0 "CFF: CID font without FDArray")
      let some [fdsD] := dictGet top 1237 | throw (.malformed 0 "CFF: CID font without FDSelect")
      let (some fdaOff, some fdsOff) := (decToNat? fdaD, decToNat? fdsD)
        | throw (.malformed 0 "CFF: bad FDArray/FDSelect offset")
      let ⟨fdIx, _⟩ ← limitIndex b fdaOff limits.maxFontDicts .fontDicts
      let fdDicts ← liftE ((fdIx.items b).mapM fun d => parseDict d 0 [] [])
      let privs ← fdDicts.mapM (parsePrivate limits.maxFontSubrs b)
      let mats ← liftE (fdDicts.mapM dictMatrix?)
      let fdA := mats.map fun
        | some m => if topM.isSome then composeA m dm else m.getD 0 z
        | none => dm.getD 0 z
      let sel ← liftE (parseFDSelect b fdsOff nGlyphs)
      pure (privs, sel, fdA)
    else do
      let p ← parsePrivate limits.maxFontSubrs b top
      pure (#[p], #[], #[])
  let fdOf (gid : Nat) : Nat := if isCID then fdSelect.getD gid privs.size else 0
  let codes := (Array.ofFn (n := nGlyphs) fun i => (i.val, (csIx.item b i.val).getD .empty)).toList
  let ev := evalList limits.glyphFuel gsubrs privs fdOf codes limits.fontFuel #[] #[]
  let glyphs := ev.1
  if glyphs.all Option.isNone then throw (.malformed 0 "CFF: no valid charstring")
  let fx (k : Nat) : Fixed := Fixed.ofDecimal (dm.getD k z)
  let bb : List Decimal := (dictGet top 5).getD []
  let bx (k : Nat) : Fixed := Fixed.ofDecimal (bb.getD k z)
  let enc := fixEncoding encoding
  return {
    name := latin1 name, isCID, ros
    fontMatrix := ⟨fx 0, fx 1, fx 2, fx 3, fx 4, fx 5⟩
    matrixA := dm.getD 0 z
    bbox := ⟨bx 0, bx 1, bx 2, bx 3⟩
    numGlyphs := nGlyphs
    maxGlyphs := limits.maxCFFGlyphs
    numGlyphs_le := csValid.1
    charset, inverse, strings
    encoding := enc.1
    encoding_size := enc.2
    fdSelect, fdMatrixA
    glyphs
    glyphs_size := by
      have h := evalList_size limits.glyphFuel gsubrs privs fdOf codes limits.fontFuel #[] #[]
      simp only [codes, Array.length_toList, Array.size_ofFn, List.size_toArray,
        List.length_nil, Nat.zero_add] at h
      exact h
    rejected := ev.2
    charstrings := codes.toArray.map (·.2)
    gsubrs, privs }

/-! ## Outlines (task 7.3a) -/

/-- The Private DICT that applies to a GID. -/
def CFFFont.privOf (f : CFFFont) (gid : Nat) : Option PrivInfo :=
  f.privs[if f.isCID then f.fdSelect.getD gid f.privs.size else 0]?

/-- Run a GID's charstring with path recording: the final state (path closed at `endchar`).
Same interpreter, same stack, nesting and fuel bounds as the metrics run. -/
def CFFFont.recordRun (f : CFFFont) (gid : Nat) (fuel : Nat) : Option CState := do
  let code ← f.charstrings[gid]?
  let priv ← f.privOf gid
  match run f.gsubrs priv.subrs fuel code 0 { record := true } with
  | .ok (st, _) => some st
  | .error _ => none

/-- The GID of a StandardEncoding code (the `endchar` accent form's operands), through the
charset. -/
def CFFFont.gidOfStdCode (f : CFFFont) (c : UInt8) : Option Nat := do
  let sid ← standardEncodingSids[c.toNat]?
  if sid == 0 then none else (f.inverse[sid]?).join

/-- **Glyph outline** of a GID in glyph space (charstring units; the font matrix maps to text
space): the path its Type 2 charstring draws from the origin. The `endchar` accent form
(TN #5177 Appendix C) is the base glyph plus the accent translated by `(adx, ady)`, both
selected by their StandardEncoding codes through the charset (name-keyed fonts; no nested
composites). `none` if the GID is missing or rejected, the charstring fails when recording,
or the outline exceeds `Outline.maxOutlineSegs`. At most `3 · fuel` charstring steps. -/
def CFFFont.outline (f : CFFFont) (gid : Nat) (fuel : Nat := Limits.default.glyphFuel) :
    Option Outline.Outline := do
  let st ← f.recordRun gid fuel
  match st.seac, st.seacArgs with
  | some (bc, ac), some (adx, ady) =>
    let bst ← f.recordRun (← f.gidOfStdCode bc) fuel
    let ast ← f.recordRun (← f.gidOfStdCode ac) fuel
    let o ← st.path.segs.append bst.path.segs
    o.append (ast.path.segs.shift adx ady)
  | _, _ => some st.path.segs

/-! ## Tests

The fixtures are `Tests/fonts/tiny.cff` and `Tests/fonts/tiny-cid.cff`, generated by
`python3 -I Tests/fonts/gen_cff.py` (see its docstring for their contents). Their expected
widths were cross-checked against fontTools' Type 2 width extractor (all glyphs except `foo`,
whose `div` it does not run, and `bad`, which it does not reject). -/

/-- Decodes a lower-case hex string (other characters ignored); test helper. -/
private def fromHex (s : String) : ByteArray :=
  let ds := s.toList.filterMap fun c =>
    if c.isDigit then some (c.toNat - 48)
    else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 87) else none
  let rec go : List Nat → ByteArray → ByteArray
    | h :: l :: r, acc => go r (acc.push (h * 16 + l).toUInt8)
    | _, acc => acc
  go ds ByteArray.empty

/-- The name-keyed fixture `tiny.cff`. -/
private def tinyCff : ByteArray := fromHex "
  010004020001020001000f5361666550646654696e79434646000102000100421d00000187001e1c3f8b8b1ea001ff8b
  8b0c07811dffffff381d000003e81d00000384051d0000007b0f1d00000088101d00000094111d0000001a1d000000d7
  12000202000100040007666f6f626164000102000100058bef050b000001002200230024018701888006204142436678
  016100220007020001000500080016001c0022002d00318b8b150efbf20ebd959fa9b3018c8d13c09090150e200a1520
  1d0e958b8bcccd0eff00008000bd8d0c0c160e8c8d000e1d000001f4141d00000258151e0a039625ff0c091d0000001a
  1300010200010005ef959f0b"

/-- The CID-keyed fixture `tiny-cid.cff`. -/
private def tinyCid : ByteArray := fromHex "
  010004020001020001000f5361666550646654696e79434944000102000100301d000001871d000001888b0c1e8c8b8b
  8c8b8b0c071d000000670f1d0000007b111d000000960c241d000000700c2500020200010006000e41646f6265496465
  6e7469747900000200010000006400010300020000000002010004000402000100050008000d000f8b8b150ef8880e8b
  8b8b150e200a0002020001001a00331ea001ff8b8b1ea001ff8b8b0c071d000000081d000000d1121ea0005f8b8b1ea0
  005f8b8b0c071d000000121d000000d9121d000003e8148b151d000007d0141d000003e8151d00000012130001020001
  0004f75c0e"

/-- Raw value of an optional `Fixed`; test helper. -/
private def rawOf (x : Option Fixed) : Option Int := x.map (·.raw)

/-- Summary of a name-keyed parse: name, glyph names, widths, rejected GIDs, per-code
(GID, advance, glyph name) for codes 32 65 66 67 97 102 120 0, the accent form of `C`. -/
private def summary (r : Except Error CFFFont) :
    Option (String × List (Option String) × List (Option Int) × List Nat ×
      List (Option Nat × Option Int × Option String) × Option (Option (UInt8 × UInt8))) :=
  match r with
  | .ok f => some (f.name, (List.range 7).map f.glyphName?,
      (List.range 7).map fun g => rawOf (f.widthOfGid g), f.rejected.toList.map (·.1),
      ([32, 65, 66, 67, 97, 102, 120, 0] : List UInt8).map fun c =>
        (f.gidOfCode c, rawOf (f.advance c), f.glyphNameOfCode c),
      (f.glyph? 4).map (·.seac))
  | .error _ => none

/-- Summary of a CID-keyed parse: name, ROS, charset, FDSelect, widths, per-CID (GID,
advance) for CIDs 0 1 100 101 2. -/
private def summaryCID (r : Except Error CFFFont) :
    Option (String × Option (String × String × Nat) × List Nat × List Nat ×
      List (Option Int) × List (Option Nat × Option Int)) :=
  match r with
  | .ok f => some (f.name, f.ros, f.charset.toList, f.fdSelect.toList,
      (List.range 4).map fun g => rawOf (f.widthOfGid g),
      ([0, 1, 100, 101, 2] : List Nat).map fun c => (f.gidOfCID c, rawOf (f.advanceOfCID c)))
  | .error _ => none

/-- Whether a parse failed. -/
private def fails (r : Except Error CFFFont) : Bool := r.toOption.isNone

/-- Run one charstring alone (no subroutines, zero widths) and return its width; test helper. -/
private def width1 (code : List UInt8) (g : Array ByteArray := #[]) : Option Int :=
  (evalGlyph g {} Limits.default.glyphFuel ⟨code.toArray⟩).toOption.map (·.1.width.raw)

#guard tinyCff.size == 252
#guard tinyCid.size == 245
#guard standardStrings.size == nStdStrings
#guard standardEncodingSids.size == 256 && expertEncodingSids.size == 256
#guard expertCharsetSids.size == 166 && expertSubsetCharsetSids.size == 87
#guard standardStrings[34]? == some "A" && standardStrings[390]? == some "Semibold"

#guard summary (parse Limits.default tinyCff) == some ("SafePdfTinyCFF",
  [".notdef", "space", "A", "B", "C", "foo", "bad"].map some,
  [some 500000000, some 250000000, some 650000000, some 700000000, some 610000000,
   some 600500000, none], [6],
  [(some 1, some 250000, some "space"), (some 2, some 650000, some "A"),
   (some 3, some 700000, some "B"), (some 4, some 610000, some "C"),
   (some 2, some 650000, some "A"), (some 5, some 600500, some "foo"),
   (some 6, none, some "bad"), (none, none, none)],
  some (some (65, 66)))
#guard (parse Limits.default tinyCff).toOption.map (fun f =>
  (f.matrixA, f.bbox.llx.raw, f.bbox.ury.raw, f.isCID, f.gidOfName? "foo", f.gidOfCID 3)) ==
  some (⟨1, 3⟩, -10000000, 900000000, false, some 5, some 3)

#guard summaryCID (parse Limits.default tinyCid) == some ("SafePdfTinyCID",
  some ("Adobe", "Identity", 0), [0, 1, 100, 101], [0, 0, 1, 1],
  [1000000000, 500000000, 1000000000, 1200000000].map some,
  [(some 0, some 1000000), (some 1, some 500000), (some 2, some 500000),
   (some 3, some 600000), (none, none)])

-- whole-font failures: empty, truncated, over the size limit, CFF2, bad major version
#guard fails (parse Limits.default ByteArray.empty)
#guard fails (parse Limits.default (tinyCff.extract 0 100))
#guard fails (parse Limits.default (tinyCid.extract 0 200))
#guard fails (parse { maxDecodedStreamBytes := 100 } tinyCff)
#guard match parse Limits.default ⟨#[2, 0, 5, 0, 0]⟩ with
  | .error (.unsupported _) => true
  | _ => false
#guard fails (parse Limits.default ⟨#[3, 0, 4, 2, 0, 0]⟩)

-- INDEX validation: count cap, offSize, first offset, bounds, empty INDEX
#guard (parseIndex ⟨#[0, 2, 1, 1, 2, 3, 65, 66]⟩ 0 2).toOption.map (·.1.count) == some 2
#guard (parseIndex ⟨#[0, 2, 1, 1, 2, 3, 65, 66]⟩ 0 1).toOption.isNone
#guard (parseIndex ⟨#[0, 1, 5, 1, 2, 65]⟩ 0 9).toOption.isNone
#guard (parseIndex ⟨#[0, 1, 1, 2, 3, 65, 66]⟩ 0 9).toOption.isNone
#guard (parseIndex ⟨#[0, 1, 1, 1, 9, 65]⟩ 0 9).toOption.isNone
#guard (parseIndex ⟨#[0, 2, 1, 1, 3, 2, 65, 66]⟩ 0 9).toOption.isNone
#guard (parseIndex ⟨#[0, 0]⟩ 0 9).toOption.map (·.1.endPos) == some 2
#guard (parseIndex ⟨#[0, 2, 1, 1, 2, 3, 65, 66]⟩ 0 9).toOption.map (fun ⟨ix, _⟩ =>
  (ix.items ⟨#[0, 2, 1, 1, 2, 3, 65, 66]⟩).toList.map (·.toList)) == some [[65], [66]]

-- DICT numbers: reals, exponents, integers
#guard (parseDict ⟨#[30, 0x1c, 0x3f, 30, 0x0a, 0x03, 0x96, 0x25, 0xff, 12, 7]⟩ 0 [] []).toOption
  ==
  some [(1207, [⟨1, 3⟩, ⟨39625, 6⟩])]
#guard (parseDict ⟨#[30, 0xe2, 0xa5, 0xb2, 0xff, 1]⟩ 0 [] []).toOption ==
  some [(1, [⟨-250, 0⟩])]
#guard (parseDict ⟨#[30, 0x1b, 0x99, 0xff, 1]⟩ 0 [] []).toOption.isNone
#guard (parseDict ⟨#[28, 0xff, 0x9c, 29, 0, 1, 0, 0, 247, 0, 251, 0, 5]⟩ 0 [] []).toOption ==
  some [(5, [⟨-100, 0⟩, ⟨65536, 0⟩, ⟨108, 0⟩, ⟨-108, 0⟩])]
#guard (parseDict ⟨#[139, 139]⟩ 0 [] []).toOption.isNone
#guard (parseDict ⟨(Array.replicate 49 139).push 5⟩ 0 [] []).toOption.isNone

-- charstrings: width rule, failures
#guard bias 100 == 107 && bias 1240 == 1131 && bias 33900 == 32768
#guard width1 [14] == some 0
#guard width1 [189, 14] == some 50000000
#guard width1 [189, 139, 139, 21, 14] == some 50000000
#guard width1 [139, 139, 21, 14] == some 0
#guard width1 [189, 139, 22, 14] == some 50000000
#guard width1 [189, 139, 140, 1, 14] == some 50000000
#guard (width1 ((List.replicate 49 139) ++ [14])).isNone
#guard (width1 [139, 139]).isNone
#guard (width1 [139, 139, 0, 14]).isNone
#guard (width1 [139, 139, 12, 12, 14]).isNone
#guard (width1 [139, 139, 12, 23, 14]).isNone
#guard (width1 [139, 140, 1, 19]).isNone
#guard width1 [139, 140, 1, 19, 0, 14] == some 0
#guard (width1 [139, 139, 139, 138, 14]).isNone
#guard (width1 [0x20, 10]).isNone
#guard (width1 [0x20, 29] #[⟨#[0x20, 29]⟩]).isNone
#guard (width1 [0x20, 29] #[⟨#[11]⟩]).isNone
#guard width1 [0x20, 29, 14] #[⟨#[11]⟩] == some 0
#guard width1 [0x20, 29, 14] #[⟨#[]⟩] == some 0
#guard width1 [255, 0, 1, 0x80, 0, 14] == some 1500000
#guard (evalGlyph #[] {} 3 ⟨#[139, 139, 139, 139, 14]⟩).toOption.isNone
#guard (evalGlyph #[] {} 5 ⟨#[139, 139, 21, 14]⟩).toOption.map (·.2) == some 4

-- the font-wide budget rejects glyphs once spent
#guard (evalList Limits.default.glyphFuel #[] #[{}] (fun _ => 0)
  [(0, ⟨#[139, 14]⟩), (1, ⟨#[14]⟩)] 2 #[] #[]).2.map
  (·.1) == #[1]

-- resource limits (task 6.2b): glyph count, Subrs count, Font DICT count, font-wide fuel
#guard match parse { maxCFFGlyphs := 6 } tinyCff with
  | .error (.limitExceeded .fontGlyphs) => true
  | _ => false
#guard (parse { maxCFFGlyphs := 7 } tinyCff).toOption.map (·.maxGlyphs) == some 7
#guard match parse { maxFontSubrs := 0 } tinyCff with
  | .error (.limitExceeded .fontSubrs) => true
  | _ => false
#guard match parse { maxFontDicts := 1 } tinyCid with
  | .error (.limitExceeded .fontDicts) => true
  | _ => false
#guard (parse { maxFontDicts := 2 } tinyCid).toOption.isSome
#guard (parse { fontFuel := 1 } tinyCff).toOption.isNone
#guard (parse { fontFuel := 40 } tinyCff).toOption.map (·.rejected.toList.map (·.1)) ==
  some [5, 6]
#guard (parse { glyphFuel := 1 } tinyCff).toOption.isSome == false

-- outlines (task 7.3a): A is a bare move to (5, 5); B a move to (10, 20) after the width
-- operand and a line by a global subr; C = A + B (endchar accent form, offset (0, 0)); foo a
-- move by 25 after the 16.16 width; bad is rejected
#guard (parse Limits.default tinyCff).toOption.map (fun f =>
  (List.range 8).map fun g => (f.outline g).map fun o => (o.1.size, o.bboxUnits)) ==
  some [some (2, some (0, 0, 0, 0)), some (0, none), some (2, some (5, 5, 5, 5)),
    some (3, some (10, 20, 10, 120)), some (5, some (5, 5, 10, 120)),
    some (2, some (25, 0, 25, 0)), none, none]
#guard (parse Limits.default tinyCid).toOption.map (fun f =>
  (List.range 4).map fun g => (f.outline g).map (·.1.size)) ==
  some [some 2, some 0, some 2, some 0]

/-- Run a charstring alone with path recording; size and bbox of the outline. -/
private def rec1 (code : List UInt8) : Option (Nat × Option (Int × Int × Int × Int)) :=
  match run #[] #[] 1000 ⟨code.toArray⟩ 0 { record := true } with
  | .ok (st, _) => some (st.path.segs.1.size, st.path.segs.bboxUnits)
  | .error _ => none

-- rmoveto, rlineto ×2, hhcurveto (odd), vhcurveto, rcurveline, flex, hflex; ends at (70, 71)
#guard rec1 [139, 139, 21,  149, 159, 169, 179, 5,  140, 141, 142, 143, 144, 27,
  140, 141, 142, 143, 30,  140, 139, 139, 139, 139, 140, 140, 140, 24,
  140, 139, 140, 139, 140, 139, 140, 139, 140, 139, 140, 139, 189, 12, 35,
  140, 140, 139, 140, 140, 140, 140, 12, 34, 14] == some (12, some (0, 0, 70, 71))
-- vvcurveto (odd), hvcurveto, rlinecurve, hflex1, flex1; ends at (26, 44)
#guard rec1 [139, 139, 21,  140, 141, 142, 143, 144, 26,  140, 141, 142, 143, 31,
  140, 140, 141, 142, 143, 144, 145, 146, 25,
  140, 140, 140, 140, 140, 140, 140, 140, 140, 12, 36,
  140, 140, 140, 140, 140, 140, 140, 140, 140, 140, 144, 12, 37, 14] == some (10, some (0, 0, 31, 44))
-- recording does not change the metrics: the width of a moving glyph is still taken
#guard width1 [149, 139, 139, 21, 14] == some 10000000

end SafePdf.Core.Font.CFF
