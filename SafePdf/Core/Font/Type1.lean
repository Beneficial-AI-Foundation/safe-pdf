import SafePdf.Core.Error
import SafePdf.Core.Limits
import SafePdf.Core.Object
import SafePdf.Core.Content.GState

/-!
# Embedded Type 1 fonts: metrics (Plan.md §6 Phase 6, task 6.3; Adobe Type 1 Font Format)

Parses an embedded Type 1 font program (ISO 32000-2 §9.9 `/FontFile`, already Flate-decoded by
the caller) far enough to give **text extraction and glyph positions** what they need: the font
name, `/FontMatrix`, `/FontBBox`, the built-in `/Encoding`, and each glyph's advance width from
its charstring's `hsbw`/`sbw`. Outlines (the full charstring path interpreter) are Phase 7.
References are to *Adobe Type 1 Font Format* (Adobe Systems, 1990): §2 (font program
structure), §6 (charstring encoding and operators), §7 (encryption), §8 (`/Private`), and
Adobe Tech Note #5040 (*Supporting Downloadable PostScript Fonts*, PFB segments).

Fonts are untrusted input (Plan.md §6: Duqu came in through font parsing), so this module
follows the core discipline: pure, every loop structural or decreasing on `size - position`,
every byte read bounds-checked (`bs[i]?`, `extract`), every charstring run fuel-bounded.

## Pipeline

1. `split`: clear-text part and eexec ciphertext. A PFB file (first byte `0x80`) is split by its
   segment headers (`pfbAux`). Otherwise the ciphertext starts after `eexec` and its following
   whitespace; `/Length1` is used when it agrees with that position (within 4 whitespace
   bytes), and `/Length2` bounds the ciphertext when it fits, else it runs to the end (the
   trailer of zeros decrypts to junk after `closefile`, which the tokenizer never reaches);
   a `/Length2` not followed by the trailer (`trailerAt`) is ignored.
   A ciphertext whose first 4 bytes are hex digits is hex-decoded first (`hexDecode`).
2. `eexecDecrypt` (§7.1–7.2: `r = 55665`, `c1 = 52845`, `c2 = 22719`, drop 4 bytes), with
   `UInt16` arithmetic (wraps mod 2¹⁶ as the spec requires, no GMP).
3. `tokenize`: a small PostScript tokenizer (names, numbers, strings, brackets, comments) that
   turns `n RD ‹n bytes›` (also `-|`) into a binary blob; it stops after `closefile`.
4. `scanClear` / `scanPrivate`: pattern scans over the token list for `/FontName`,
   `/FontMatrix`, `/FontBBox`, `/Encoding` (`StandardEncoding` or `dup c /name put`),
   `/lenIV`, `/Subrs` entries (`dup i n RD …`) and `/CharStrings` entries (`/name n RD …`).
5. `run`: the metrics charstring interpreter. It executes every operator (to validate the
   charstring) but only records `hsbw`/`sbw` (side bearing, advance) and `seac`; path
   operators only clear the stack. A glyph is **rejected** (listed in `Font1.rejected`, never
   fatal) on: stack overflow (`maxStack = 24`, §6.1), stack underflow, subroutine nesting
   deeper than `maxCallDepth = 10` (§6.4), a bad subroutine index, an unknown operator, a
   truncated number, division by zero, running off the end without `endchar`/`return`, more
   than `glyphFuel` operations, or no `hsbw`/`sbw`.

## Bounds and caps

* Input ≤ `Limits.maxDecodedStreamBytes` (else `Error.limitExceeded .decodedStreamBytes`).
* At most `maxGlyphs = 4096` charstrings and subroutine indices `< maxSubrs = 32768`. `Limits`
  has no font-specific `LimitKind`, so exceeding these is reported as `Error.malformed`.
* Numbers in the font program have at most 18 digits (longer tokens are names), so every
  `Decimal` has scale ≤ 18 and the exact advance computation stays small.

## What is skipped

`/OtherSubrs` code, hints, `/FontInfo`, `/UniqueID`, flex details: `callothersubr`/`pop` only
move numbers between the two stacks (`pop` on an empty PostScript stack pushes 0). Fonts with
duplicate `/CharStrings` keys use the first definition. Radix and exponent numbers are names.

## Results

`Font1` holds the parsed data with 256-entry `encoding` and `advances` arrays (sizes as proof
fields). `Font1.advance code` is the text-space advance (`wx·a + wy·c` of the exact
`/FontMatrix` entries, rounded once to `Fixed`), i.e. `wx / 1000` for the usual matrix: what
`Core.Content.Interp.Config.advance` will consume (task 6.5).

## Theorems

`decrypt_size`, `eexecDecrypt_size`, `decryptCharstring_size` (length laws);
`scanWhile_bounds`, `scanString_bounds`, `nextTok_spec` (each token advances and ends within
the input, so `tokenize` terminates and never reads past the input); `run_stack_le`,
`run_calls_le` (stack and call-depth bounds hold by construction); `Font1.advance_eq`.
-/

namespace SafePdf.Core.Font.Type1

open SafePdf SafePdf.Core.Content

/-! ## Encryption (§7) -/

/-- The eexec initial key `r = 55665` (§7.2). -/
def eexecKey : UInt16 := 55665

/-- The charstring initial key `r = 4330` (§7.3). -/
def charstringKey : UInt16 := 4330

/-- The next cipher key after ciphertext byte `c` under key `r`: `(c + r)·52845 + 22719 mod 2¹⁶`
(§7.1). -/
def nextKey (r : UInt16) (c : UInt8) : UInt16 := (c.toUInt16 + r) * 52845 + 22719

/-- Decryption loop: decrypts `data[i…]` under key `r`, dropping plaintext bytes at positions
`< skip`, appending to `out`. -/
def decryptAux (data : ByteArray) (skip : Nat) (i : Nat) (r : UInt16) (out : ByteArray) :
    ByteArray :=
  if h : i < data.size then
    let c := data[i]
    let p := c ^^^ (r >>> 8).toUInt8
    decryptAux data skip (i + 1) (nextKey r c) (if i < skip then out else out.push p)
  else out
termination_by data.size - i

/-- Type 1 decryption of `data` with initial key `r`, dropping the first `skip` plaintext bytes
(§7.1). -/
def decrypt (r : UInt16) (skip : Nat) (data : ByteArray) : ByteArray :=
  decryptAux data skip 0 r ByteArray.empty

/-- Size law of the decryption loop. -/
theorem decryptAux_size (data : ByteArray) (skip : Nat) :
    ∀ (n i : Nat) (r : UInt16) (out : ByteArray), data.size - i = n →
      (decryptAux data skip i r out).size = out.size + (data.size - max i skip) := by
  intro n
  induction n with
  | zero =>
    intro i r out hn
    rw [decryptAux.eq_def]
    have : ¬ i < data.size := by omega
    simp only [this, dite_false]
    omega
  | succ n ih =>
    intro i r out hn
    rw [decryptAux.eq_def]
    have hi : i < data.size := by omega
    simp only [hi, dite_true]
    rw [ih (i + 1) _ _ (by omega)]
    by_cases hs : i < skip
    · simp only [hs, ite_true]; omega
    · simp only [hs, ite_false, ByteArray.size_push]; omega

/-- **Length law**: decryption drops exactly `skip` bytes (or everything if shorter). -/
theorem decrypt_size (r : UInt16) (skip : Nat) (data : ByteArray) :
    (decrypt r skip data).size = data.size - skip := by
  unfold decrypt
  rw [decryptAux_size data skip _ 0 r ByteArray.empty rfl]
  have : ByteArray.empty.size = 0 := rfl
  omega

/-- eexec decryption of the private part: key 55665, 4 lead bytes dropped (§7.2). -/
def eexecDecrypt (data : ByteArray) : ByteArray := decrypt eexecKey 4 data

/-- **Length law**: `eexecDecrypt` output length = input length − 4. -/
theorem eexecDecrypt_size (data : ByteArray) : (eexecDecrypt data).size = data.size - 4 :=
  decrypt_size _ _ _

/-- Charstring decryption: key 4330, `lenIV` lead bytes dropped; a negative `lenIV` means the
charstrings are not encrypted (§7.3, §8 `lenIV`). -/
def decryptCharstring (lenIV : Int) (data : ByteArray) : ByteArray :=
  if lenIV < 0 then data else decrypt charstringKey lenIV.toNat data

/-- **Length law** for charstrings. -/
theorem decryptCharstring_size (lenIV : Int) (data : ByteArray) (h : 0 ≤ lenIV) :
    (decryptCharstring lenIV data).size = data.size - lenIV.toNat := by
  unfold decryptCharstring
  have : ¬ lenIV < 0 := by omega
  simp only [this, ite_false, decrypt_size]

/-- Encryption loop (inverse of `decryptAux` with `skip = 0`); used to build test fixtures. -/
def encryptAux (data : ByteArray) (i : Nat) (r : UInt16) (out : ByteArray) : ByteArray :=
  if h : i < data.size then
    let c := data[i] ^^^ (r >>> 8).toUInt8
    encryptAux data (i + 1) (nextKey r c) (out.push c)
  else out
termination_by data.size - i

/-- Type 1 encryption of `lead ++ data` with initial key `r` (§7.1); test-fixture helper. -/
def encrypt (r : UInt16) (lead data : ByteArray) : ByteArray :=
  encryptAux (lead ++ data) 0 r ByteArray.empty

/-! ## Byte classes and small scanners -/

/-- PostScript whitespace: space, tab, LF, CR, FF, NUL. -/
def isWs (c : UInt8) : Bool := c == 32 || c == 10 || c == 13 || c == 9 || c == 12 || c == 0

/-- The whitespace allowed between `eexec` and the ciphertext: space, tab, LF, CR. -/
def isEexecWs (c : UInt8) : Bool := c == 32 || c == 10 || c == 13 || c == 9

/-- PostScript delimiters `( ) < > [ ] { } / %`. -/
def isDelim (c : UInt8) : Bool :=
  c == 40 || c == 41 || c == 60 || c == 62 || c == 91 || c == 93 || c == 123 || c == 125 ||
  c == 47 || c == 37

/-- Regular characters: neither whitespace nor delimiter. -/
def isRegular (c : UInt8) : Bool := !isWs c && !isDelim c

/-- The value of a hex digit. -/
def hexVal (c : UInt8) : Option UInt8 :=
  if 48 ≤ c ∧ c ≤ 57 then some (c - 48)
  else if 65 ≤ c ∧ c ≤ 70 then some (c - 55)
  else if 97 ≤ c ∧ c ≤ 102 then some (c - 87)
  else none

/-- The first position `≥ i` whose byte fails `p` (or the end). -/
def scanWhile (p : UInt8 → Bool) (s : ByteArray) (i : Nat) : Nat :=
  if h : i < s.size then (if p s[i] then scanWhile p s (i + 1) else i) else i
termination_by s.size - i

/-- `scanWhile` never moves backwards and never passes the end (from inside the input). -/
theorem scanWhile_bounds (p : UInt8 → Bool) (s : ByteArray) (i : Nat) :
    i ≤ scanWhile p s i ∧ scanWhile p s i ≤ max i s.size := by
  fun_induction scanWhile p s i <;> omega

/-- The position after the `)` closing a PostScript string whose body starts at `i`, with
nesting `depth` and `\` escapes (§2 / PLRM §3.2.2); the end of input if unterminated. -/
def scanString (s : ByteArray) (i depth : Nat) : Nat :=
  if h : i < s.size then
    let c := s[i]
    if c == 92 then scanString s (min (i + 2) s.size) depth
    else if c == 40 then scanString s (i + 1) (depth + 1)
    else if c == 41 then (if depth = 0 then i + 1 else scanString s (i + 1) (depth - 1))
    else scanString s (i + 1) depth
  else max i s.size
termination_by s.size - i

/-- `scanString` never moves backwards and never passes the end (from inside the input). -/
theorem scanString_bounds (s : ByteArray) (i depth : Nat) :
    i ≤ scanString s i depth ∧ scanString s i depth ≤ max i s.size := by
  fun_induction scanString s i depth <;> omega

/-- Decode hex digits from `i` on (whitespace ignored), stopping at the first other byte; a
dangling final digit is dropped. -/
def hexDecodeAux (s : ByteArray) (i : Nat) (hi : Option UInt8) (out : ByteArray) : ByteArray :=
  if h : i < s.size then
    let c := s[i]
    if isWs c then hexDecodeAux s (i + 1) hi out
    else match hexVal c, hi with
      | none, _ => out
      | some v, none => hexDecodeAux s (i + 1) (some v) out
      | some v, some u => hexDecodeAux s (i + 1) none (out.push (u * 16 + v))
  else out
termination_by s.size - i

/-- Hex-decode a hex eexec section (§7.2). -/
def hexDecode (s : ByteArray) : ByteArray := hexDecodeAux s 0 none ByteArray.empty

/-- Whether `pat` occurs in `s` at `i`. -/
def matchAt (s : ByteArray) (i : Nat) : List UInt8 → Bool
  | [] => true
  | c :: cs => s[i]? == some c && matchAt s (i + 1) cs

/-- The first occurrence of `pat` in `s` at or after `i`. -/
def findSub (s : ByteArray) (pat : List UInt8) (i : Nat) : Option Nat :=
  if i < s.size then (if matchAt s i pat then some i else findSub s pat (i + 1)) else none
termination_by s.size - i

/-! ## Splitting the font program (§2, §7.2; Tech Note #5040) -/

/-- The clear-text part and the (binary, decoded from hex if needed) eexec ciphertext. -/
structure Parts where
  /-- The clear-text part, through `eexec` and its whitespace. -/
  clear : ByteArray
  /-- The eexec-encrypted part (binary). -/
  cipher : ByteArray

/-- A little-endian 32-bit length at `i` (PFB segment header); missing bytes read as 0. -/
def le32 (s : ByteArray) (i : Nat) : Nat :=
  (s[i]?.getD 0).toNat + (s[i + 1]?.getD 0).toNat * 256 + (s[i + 2]?.getD 0).toNat * 65536 +
    (s[i + 3]?.getD 0).toNat * 16777216

/-- Walk PFB segments from `i`: ASCII segments (type 1) before the first binary segment form
the clear text, binary segments (type 2) the ciphertext; a later ASCII segment (the trailer),
type 3 (EOF), or a bad header ends the walk. Segment lengths are clamped to the input. -/
def pfbAux (s : ByteArray) (i : Nat) (clear cipher : ByteArray) : ByteArray × ByteArray :=
  if _h : i + 6 ≤ s.size ∧ s[i]? = some 0x80 then
    let t := s[i + 1]?.getD 0
    let e := min (i + 6 + le32 s (i + 2)) s.size
    let seg := s.extract (i + 6) e
    if t == 1 then
      (if cipher.size == 0 then pfbAux s e (clear ++ seg) cipher else (clear, cipher))
    else if t == 2 then pfbAux s e clear (cipher ++ seg)
    else (clear, cipher)
  else (clear, cipher)
termination_by s.size - i

/-- The bytes of an ASCII string literal. -/
def ascii (str : String) : List UInt8 := str.toUTF8.toList

/-- Whether all bytes of `s` in `[a, b)` are eexec whitespace. -/
def allEexecWs (s : ByteArray) (a b : Nat) : Bool :=
  (List.range (b - a)).all fun k => isEexecWs (s[a + k]?.getD 0)

/-- Whether a ciphertext region is hex-encoded: its first 4 bytes are hex digits (§7.2). -/
def isHexStart (s : ByteArray) : Bool :=
  4 ≤ s.size && (List.range 4).all fun k => (hexVal (s[k]?.getD 0)).isSome

/-- Whether position `k` plausibly ends the eexec section: after whitespace comes the end of
the data, a `0` (the trailer of zeros) or `cleartomark`. A `/Length2` that fails this check is
wrong and ignored (the section then runs to the end, which is harmless: decryption of the
trailer yields bytes after `closefile`, which the tokenizer never reads). -/
def trailerAt (s : ByteArray) (k : Nat) : Bool :=
  let p := scanWhile isWs s k
  match s[p]? with
  | none => true
  | some c => c == 48 || matchAt s p (ascii "cleartomark")

/-- Split a `/FontFile` stream into clear text and binary ciphertext, given the stream
dictionary's `/Length1` and `/Length2` (either may be absent or wrong). -/
def split (s : ByteArray) (len1 len2 : Option Nat) : Except Error Parts :=
  if s[0]? == some 0x80 then
    let (c, b) := pfbAux s 0 ByteArray.empty ByteArray.empty
    if b.size == 0 then .error (.malformed 0 "Type 1: PFB file without a binary segment")
    else .ok ⟨c, b⟩
  else
    let e? := match findSub s (ascii "currentfile eexec") 0 with
      | some p => some (p + 17)
      | none => (findSub s (ascii "eexec") 0).map (· + 5)
    match e? with
    | none => .error (.malformed 0 "Type 1: no eexec section")
    | some e =>
      let start := match len1 with
        | some l =>
          if e ≤ l ∧ l ≤ e + 4 ∧ l ≤ s.size ∧ allEexecWs s e l = true then l
          else scanWhile isEexecWs s e
        | none => scanWhile isEexecWs s e
      let stop := match len2 with
        | some l => if 0 < l ∧ start + l ≤ s.size ∧ trailerAt s (start + l) then start + l
          else s.size
        | none => s.size
      let region := s.extract start stop
      .ok ⟨s.extract 0 start, if isHexStart region then hexDecode region else region⟩

/-! ## PostScript tokens -/

/-- A PostScript token, as far as the font parser needs it. -/
inductive Tok where
  /-- A literal name `/name`. -/
  | lit (name : String)
  /-- An executable name. -/
  | exe (name : String)
  /-- An integer. -/
  | int (v : Int)
  /-- A real number (exact decimal). -/
  | real (d : Decimal)
  /-- `[` -/
  | lbrack
  /-- `]` -/
  | rbrack
  /-- `{` -/
  | lbrace
  /-- `}` -/
  | rbrace
  /-- Anything else (strings, `<<`, `>>`, stray delimiters). -/
  | other
  deriving Repr, Inhabited, BEq

/-- A name from raw bytes (each byte one character, so always valid). -/
def nameOf (w : List UInt8) : String := String.ofList (w.map fun b => Char.ofNat b.toNat)

/-- Digits of a decimal number: accumulated value, digit count, digits after the point. -/
def numDigits : List UInt8 → Nat → Nat → Option Nat → Option (Nat × Nat × Option Nat)
  | [], acc, nd, frac => if nd = 0 then none else some (acc, nd, frac)
  | c :: r, acc, nd, frac =>
    if 48 ≤ c ∧ c ≤ 57 then
      numDigits r (acc * 10 + (c - 48).toNat) (nd + 1) (frac.map (· + 1))
    else if c == 46 ∧ frac.isNone then numDigits r acc nd (some 0)
    else none

/-- Parse a decimal number token (`[+-]digits[.digits]`, at most 18 digits): the value and
whether it was written as an integer. -/
def parseNum (w : List UInt8) : Option (Decimal × Bool) :=
  let (neg, rest) := match w with
    | 45 :: r => (true, r)
    | 43 :: r => (false, r)
    | r => (false, r)
  match numDigits rest 0 0 none with
  | some (acc, nd, frac) =>
    if nd ≤ 18 then
      let m : Int := if neg then -(acc : Int) else acc
      some (⟨m, frac.getD 0⟩, frac.isNone)
    else none
  | none => none

/-- Classify a regular word: a number or an executable name. -/
def classify (w : List UInt8) : Tok :=
  match parseNum w with
  | some (d, true) => .int d.mantissa
  | some (d, false) => .real d
  | none => .exe (nameOf w)

/-- The bytes of `s` in `[a, b)`. -/
def slice (s : ByteArray) (a b : Nat) : List UInt8 := (s.extract a b).toList

/-- The token starting with the non-whitespace, non-`%` byte `c` at `i`, and the position
after it. -/
def tokAt (s : ByteArray) (i : Nat) (c : UInt8) : Tok × Nat :=
  if c == 40 then (.other, scanString s (i + 1) 0)
  else if c == 60 then
    if s[i + 1]? == some 60 then (.other, min (i + 2) s.size)
    else (.other, min (scanWhile (· != 62) s (i + 1) + 1) s.size)
  else if c == 62 then
    if s[i + 1]? == some 62 then (.other, min (i + 2) s.size) else (.other, i + 1)
  else if c == 91 then (.lbrack, i + 1)
  else if c == 93 then (.rbrack, i + 1)
  else if c == 123 then (.lbrace, i + 1)
  else if c == 125 then (.rbrace, i + 1)
  else if c == 41 then (.other, i + 1)
  else if c == 47 then
    let j := scanWhile isRegular s (i + 1)
    (.lit (nameOf (slice s (i + 1) j)), j)
  else
    let j := scanWhile isRegular s (i + 1)
    (classify (slice s i j), j)

/-- A token starting inside the input ends after its start and within the input. -/
theorem tokAt_spec (s : ByteArray) (i : Nat) (c : UInt8) (hi : i < s.size) :
    i < (tokAt s i c).2 ∧ (tokAt s i c).2 ≤ s.size := by
  have b1 := scanString_bounds s (i + 1) 0
  have b2 := scanWhile_bounds isRegular s (i + 1)
  have b3 := scanWhile_bounds (· != 62) s (i + 1)
  unfold tokAt
  repeat' split
  all_goals (dsimp only; omega)

/-- The next token at or after `i` and the position after it; `none` at the end of input.
Whitespace and `%` comments are skipped. -/
def nextTok (s : ByteArray) (i : Nat) : Option (Tok × Nat) :=
  if h : i < s.size then
    if isWs s[i] then nextTok s (i + 1)
    else if s[i] == 37 then nextTok s (scanWhile (fun b => b != 10 && b != 13) s (i + 1))
    else some (tokAt s i s[i])
  else none
termination_by s.size - i
decreasing_by
  · omega
  · have := (scanWhile_bounds (fun b => b != 10 && b != 13) s (i + 1)).1; omega

/-- **The tokenizer never reads past the input and always advances**: a token found at or
after `i` ends at a position `j` with `i < j ≤ s.size`. -/
theorem nextTok_spec (s : ByteArray) (i : Nat) {t : Tok} {j : Nat}
    (h : nextTok s i = some (t, j)) : i < j ∧ j ≤ s.size := by
  fun_induction nextTok s i with
  | case1 i hi _ ih => exact (fun ⟨a, b⟩ => ⟨by omega, b⟩) (ih h)
  | case2 i hi _ _ ih =>
    have := (scanWhile_bounds (fun b => b != 10 && b != 13) s (i + 1)).1
    exact (fun ⟨a, b⟩ => ⟨by omega, b⟩) (ih h)
  | case3 i hi _ _ =>
    have := tokAt_spec s i s[i] hi
    simp only [Option.some.injEq] at h
    rw [h] at this
    exact this
  | case4 => cases h

/-- A tokenizer item: a token, or the binary data read by `n RD ‹n bytes›`. -/
inductive Item where
  /-- A token. -/
  | tok (t : Tok)
  /-- Binary data (an encrypted charstring or subroutine). -/
  | blob (b : ByteArray)
  deriving Inhabited

/-- Whether an executable name reads binary data (`RD`, or `-|` in older fonts, §2.4). -/
def isReadName (n : String) : Bool := n == "RD" || n == "-|"

/-- Tokenize from `i`, appending to `acc`. `prevInt` is the previous token if it was a
non-negative integer: an `RD`/`-|` after it reads that many bytes after one space as a blob
(a truncated blob ends the token list). Tokenizing stops after `closefile`. -/
def tokenize (s : ByteArray) (i : Nat) (prevInt : Option Nat) (acc : Array Item) :
    Array Item :=
  match h : nextTok s i with
  | none => acc
  | some (t, j) =>
    have _hj := nextTok_spec s i h
    match t, prevInt with
    | .exe n, some len =>
      if isReadName n then
        if hb : j + 1 + len ≤ s.size then
          tokenize s (j + 1 + len) none (acc.push (.blob (s.extract (j + 1) (j + 1 + len))))
        else acc
      else if n == "closefile" then acc.push (.tok t)
      else tokenize s j none (acc.push (.tok t))
    | .exe n, none =>
      if n == "closefile" then acc.push (.tok t) else tokenize s j none (acc.push (.tok t))
    | .int v, _ => tokenize s j (if 0 ≤ v then some v.toNat else none) (acc.push (.tok t))
    | _, _ => tokenize s j none (acc.push (.tok t))
termination_by s.size - i

/-! ## Standard encoding (§2.3; ISO 32000-2 Annex D.2) -/

/-- The non-`.notdef` entries of Adobe `StandardEncoding`. -/
def standardEncodingEntries : List (Nat × String) :=
  [(32, "space"), (33, "exclam"), (34, "quotedbl"), (35, "numbersign"), (36, "dollar"),
   (37, "percent"), (38, "ampersand"), (39, "quoteright"), (40, "parenleft"),
   (41, "parenright"), (42, "asterisk"), (43, "plus"), (44, "comma"), (45, "hyphen"),
   (46, "period"), (47, "slash"), (48, "zero"), (49, "one"), (50, "two"), (51, "three"),
   (52, "four"), (53, "five"), (54, "six"), (55, "seven"), (56, "eight"), (57, "nine"),
   (58, "colon"), (59, "semicolon"), (60, "less"), (61, "equal"), (62, "greater"),
   (63, "question"), (64, "at"), (65, "A"), (66, "B"), (67, "C"), (68, "D"), (69, "E"),
   (70, "F"), (71, "G"), (72, "H"), (73, "I"), (74, "J"), (75, "K"), (76, "L"), (77, "M"),
   (78, "N"), (79, "O"), (80, "P"), (81, "Q"), (82, "R"), (83, "S"), (84, "T"), (85, "U"),
   (86, "V"), (87, "W"), (88, "X"), (89, "Y"), (90, "Z"), (91, "bracketleft"),
   (92, "backslash"), (93, "bracketright"), (94, "asciicircum"), (95, "underscore"),
   (96, "quoteleft"), (97, "a"), (98, "b"), (99, "c"), (100, "d"), (101, "e"), (102, "f"),
   (103, "g"), (104, "h"), (105, "i"), (106, "j"), (107, "k"), (108, "l"), (109, "m"),
   (110, "n"), (111, "o"), (112, "p"), (113, "q"), (114, "r"), (115, "s"), (116, "t"),
   (117, "u"), (118, "v"), (119, "w"), (120, "x"), (121, "y"), (122, "z"),
   (123, "braceleft"), (124, "bar"), (125, "braceright"), (126, "asciitilde"),
   (161, "exclamdown"), (162, "cent"), (163, "sterling"), (164, "fraction"), (165, "yen"),
   (166, "florin"), (167, "section"), (168, "currency"), (169, "quotesingle"),
   (170, "quotedblleft"), (171, "guillemotleft"), (172, "guilsinglleft"),
   (173, "guilsinglright"), (174, "fi"), (175, "fl"), (177, "endash"), (178, "dagger"),
   (179, "daggerdbl"), (180, "periodcentered"), (182, "paragraph"), (183, "bullet"),
   (184, "quotesinglbase"), (185, "quotedblbase"), (186, "quotedblright"),
   (187, "guillemotright"), (188, "ellipsis"), (189, "perthousand"), (191, "questiondown"),
   (193, "grave"), (194, "acute"), (195, "circumflex"), (196, "tilde"), (197, "macron"),
   (198, "breve"), (199, "dotaccent"), (200, "dieresis"), (202, "ring"), (203, "cedilla"),
   (205, "hungarumlaut"), (206, "ogonek"), (207, "caron"), (208, "emdash"), (225, "AE"),
   (227, "ordfeminine"), (232, "Lslash"), (233, "Oslash"), (234, "OE"),
   (235, "ordmasculine"), (241, "ae"), (245, "dotlessi"), (248, "lslash"), (249, "oslash"),
   (250, "oe"), (251, "germandbls")]

/-- A 256-entry encoding from `(code, name)` entries applied in order (later wins);
`.notdef` and out-of-range codes leave `none`. -/
def encodingOf (entries : List (Nat × String)) : Array (Option String) :=
  entries.foldl (fun a (c, n) => if n == ".notdef" then a.setIfInBounds c none
    else a.setIfInBounds c (some n)) (Array.replicate 256 none)

/-- `encodingOf` always has 256 entries. -/
theorem encodingOf_size (entries : List (Nat × String)) : (encodingOf entries).size = 256 := by
  unfold encodingOf
  suffices ∀ (l : List (Nat × String)) (a : Array (Option String)), a.size = 256 →
      (l.foldl (fun a (c, n) => if n == ".notdef" then a.setIfInBounds c none
        else a.setIfInBounds c (some n)) a).size = 256 from this _ _ (by simp)
  intro l
  induction l with
  | nil => intro a h; simpa using h
  | cons x r ih =>
    intro a h
    simp only [List.foldl_cons]
    apply ih
    split <;> simp [h]

/-! ## Clear-text and private-part scans (§2, §8) -/

/-- How the clear text defines `/Encoding`. -/
inductive EncKind where
  /-- Not seen (the default is `StandardEncoding`). -/
  | unset
  /-- `/Encoding StandardEncoding def`. -/
  | standard
  /-- An explicit array filled by `dup c /name put`. -/
  | explicit
  deriving BEq, Repr

/-- What the clear-text scan collects. -/
structure ClearInfo where
  /-- `/FontName` (first occurrence). -/
  name : Option String := none
  /-- `/FontMatrix` entries (first occurrence). -/
  matrix : Option (List Decimal) := none
  /-- `/FontBBox` entries (first occurrence). -/
  bbox : Option (List Decimal) := none
  /-- The kind of `/Encoding`. -/
  encKind : EncKind := .unset
  /-- Explicit encoding entries, latest first. -/
  entries : List (Nat × String) := []

/-- Take `k` numbers from the front of a token list. -/
def takeNums : Nat → List Item → Option (List Decimal)
  | 0, _ => some []
  | k + 1, .tok (.int v) :: r => (takeNums k r).map (⟨v, 0⟩ :: ·)
  | k + 1, .tok (.real d) :: r => (takeNums k r).map (d :: ·)
  | _, _ => none

/-- Whether an item opens an array or procedure. -/
def isOpen : Item → Bool
  | .tok .lbrack | .tok .lbrace => true
  | _ => false

/-- Scan the clear-text tokens. -/
def scanClear : List Item → ClearInfo → ClearInfo
  | [], ci => ci
  | .tok (.lit "FontName") :: .tok (.lit n) :: r, ci =>
    scanClear r { ci with name := ci.name <|> some n }
  | .tok (.lit "FontMatrix") :: o :: r, ci =>
    scanClear r (if isOpen o && ci.matrix.isNone then { ci with matrix := takeNums 6 r } else ci)
  | .tok (.lit "FontBBox") :: o :: r, ci =>
    scanClear r (if isOpen o && ci.bbox.isNone then { ci with bbox := takeNums 4 r } else ci)
  | .tok (.lit "Encoding") :: .tok (.exe "StandardEncoding") :: r, ci =>
    scanClear r { ci with encKind := .standard }
  | .tok (.lit "Encoding") :: r, ci => scanClear r { ci with encKind := .explicit }
  | .tok (.exe "dup") :: .tok (.int c) :: .tok (.lit n) :: .tok (.exe "put") :: r, ci =>
    scanClear r (if ci.encKind == .explicit && 0 ≤ c && c < 256 then
      { ci with entries := (c.toNat, n) :: ci.entries } else ci)
  | _ :: r, ci => scanClear r ci

/-- What the private-part scan collects. -/
structure PrivInfo where
  /-- `/lenIV` (default 4). -/
  lenIV : Int := 4
  /-- Whether `/CharStrings` has been seen. -/
  inCharStrings : Bool := false
  /-- Subroutines `(index, encrypted bytes)`, latest first. -/
  subrs : List (Nat × ByteArray) := []
  /-- Charstrings `(glyph name, encrypted bytes)`, latest first. -/
  charstrings : List (String × ByteArray) := []

/-- Scan the decrypted private-part tokens. -/
def scanPrivate : List Item → PrivInfo → PrivInfo
  | [], p => p
  | .tok (.lit "lenIV") :: .tok (.int v) :: r, p => scanPrivate r { p with lenIV := v }
  | .tok (.lit "CharStrings") :: r, p => scanPrivate r { p with inCharStrings := true }
  | .tok (.exe "dup") :: .tok (.int i) :: .tok (.int _) :: .blob b :: r, p =>
    scanPrivate r (if 0 ≤ i then { p with subrs := (i.toNat, b) :: p.subrs } else p)
  | .tok (.lit n) :: .tok (.int _) :: .blob b :: r, p =>
    scanPrivate r (if p.inCharStrings then { p with charstrings := (n, b) :: p.charstrings }
      else p)
  | _ :: r, p => scanPrivate r p

/-! ## Charstring interpreter for metrics (§6) -/

/-- Maximum argument-stack depth (§6.1: 24). -/
def maxStack : Nat := 24

/-- Maximum subroutine nesting (§6.4: 10). -/
def maxCallDepth : Nat := 10

/-- Maximum number of operators and operands executed per glyph, subroutines included. -/
def glyphFuel : Nat := 20000

/-- Maximum number of charstrings in one font. -/
def maxGlyphs : Nat := 4096

/-- Subroutine indices must be below this. -/
def maxSubrs : Nat := 32768

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

/-- The bottom `k` operands in push order (Type 1 operators take their arguments from the
bottom of the stack and clear it). -/
def Stack.bottom (s : Stack) (k : Nat) : Except String (List Fixed) :=
  if k ≤ s.1.length then .ok (s.1.reverse.take k) else .error "charstring stack underflow"

/-- A return address: the charstring and the position after `callsubr`. -/
structure Frame where
  /-- The calling charstring. -/
  code : ByteArray
  /-- The position to resume at. -/
  pos : Nat

/-- The interpreter state. Stack and call depth are bounded by their types. -/
structure CState where
  /-- The charstring argument stack. -/
  stack : Stack := Stack.empty
  /-- The subroutine return stack, at most `maxCallDepth` deep. -/
  calls : {l : List Frame // l.length ≤ maxCallDepth} := ⟨[], Nat.zero_le _⟩
  /-- The PostScript stack used by `callothersubr`/`pop`. -/
  ps : Stack := Stack.empty
  /-- Left side bearing `sbx`. -/
  sbx : Fixed := Fixed.zero
  /-- Advance `(wx, wy)` from `hsbw`/`sbw`. -/
  width : Option (Fixed × Fixed) := none
  /-- `seac` components `(bchar, achar)`. -/
  seac : Option (UInt8 × UInt8) := none

/-- Decode the charstring number starting with byte `v ≥ 32` at `pos` (§6.2). -/
def decodeNum (code : ByteArray) (pos : Nat) (v : UInt8) : Option (Int × Nat) :=
  if v ≤ 246 then some ((v.toNat : Int) - 139, pos + 1)
  else if v ≤ 250 then
    code[pos + 1]?.map fun w => (Int.ofNat ((v.toNat - 247) * 256 + w.toNat + 108), pos + 2)
  else if v ≤ 254 then
    code[pos + 1]?.map fun w => (-Int.ofNat ((v.toNat - 251) * 256 + w.toNat + 108), pos + 2)
  else
    match code[pos + 1]?, code[pos + 2]?, code[pos + 3]?, code[pos + 4]? with
    | some a, some b, some c, some d =>
      let u : Nat := a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat
      some (if u ≥ 2147483648 then (u : Int) - 4294967296 else u, pos + 5)
    | _, _, _, _ => none

/-- A non-negative integral `Fixed` as a `Nat`. -/
def Fixed.toNat? (x : Fixed) : Option Nat :=
  if 0 ≤ x.raw ∧ x.raw % fixedScale = 0 then some (x.raw / fixedScale).toNat else none

/-- A character code operand of `seac`. -/
def toCode? (x : Fixed) : Option UInt8 :=
  match Fixed.toNat? x with
  | some n => if n < 256 then some n.toUInt8 else none
  | none => none

/-- Run a charstring (§6.4–6.5) from `pos` with at most `fuel` steps, returning the state at
`endchar`/`seac`. Path and hint operators only clear the stack; `hsbw`/`sbw` record metrics;
`callsubr`/`return` use the bounded call stack. Every failure is an error message. -/
def run (subrs : Array ByteArray) : Nat → ByteArray → Nat → CState → Except String CState
  | 0, _, _, _ => .error "charstring fuel exhausted"
  | fuel + 1, code, pos, st =>
    match code[pos]? with
    | none => .error "charstring ends without endchar or return"
    | some v =>
      if 32 ≤ v then
        match decodeNum code pos v with
        | none => .error "truncated charstring number"
        | some (n, pos') => do
          let stk ← st.stack.push (Fixed.ofInt n)
          run subrs fuel code pos' { st with stack := stk }
      else if v == 12 then
        match code[pos + 1]? with
        | none => .error "truncated escape operator"
        | some w =>
          let clear := { st with stack := Stack.empty }
          if w == 0 || w == 1 || w == 2 then run subrs fuel code (pos + 2) clear
          else if w == 6 then do
            -- seac: asb adx ady bchar achar
            let args ← st.stack.bottom 5
            match toCode? (args.getD 3 Fixed.zero), toCode? (args.getD 4 Fixed.zero) with
            | some b, some a => .ok { clear with seac := some (b, a) }
            | _, _ => .error "seac: bad character code"
          else if w == 7 then do
            -- sbw: sbx sby wx wy
            let args ← st.stack.bottom 4
            run subrs fuel code (pos + 2) { clear with
              sbx := args.getD 0 Fixed.zero,
              width := some (args.getD 2 Fixed.zero, args.getD 3 Fixed.zero) }
          else if w == 12 then do
            let (b, s1) ← st.stack.pop
            let (a, s2) ← s1.pop
            if b.raw = 0 then .error "charstring division by zero"
            else
              let s3 ← s2.push (Fixed.div a b)
              run subrs fuel code (pos + 2) { st with stack := s3 }
          else if w == 16 then do
            let (_, s1) ← st.stack.pop
            let (nx, s2) ← s1.pop
            match Fixed.toNat? nx with
            | none => .error "callothersubr: bad argument count"
            | some n =>
              if n ≤ s2.1.length then
                let ps : Stack := ⟨s2.1.take n, by
                  have := s2.2; simp only [List.length_take]; omega⟩
                let rest : Stack := ⟨s2.1.drop n, by
                  have := s2.2; simp only [List.length_drop]; omega⟩
                run subrs fuel code (pos + 2) { st with stack := rest, ps := ps }
              else .error "callothersubr: stack underflow"
          else if w == 17 then do
            let (x, ps') := match st.ps.pop with
              | .ok r => r
              | .error _ => (Fixed.zero, Stack.empty)
            let s1 ← st.stack.push x
            run subrs fuel code (pos + 2) { st with stack := s1, ps := ps' }
          else if w == 33 then run subrs fuel code (pos + 2) clear
          else .error "unknown escape operator"
      else if v == 10 then do
        let (ix, s1) ← st.stack.pop
        match (Fixed.toNat? ix).bind (subrs[·]?) with
        | none => .error "callsubr: bad subroutine index"
        | some sub =>
          if h : st.calls.1.length < maxCallDepth then
            run subrs fuel sub 0
              { st with stack := s1, calls := ⟨⟨code, pos + 1⟩ :: st.calls.1, h⟩ }
          else .error "callsubr: subroutines nested too deep"
      else if v == 11 then
        match st.calls with
        | ⟨f :: fs, h⟩ =>
          run subrs fuel f.code f.pos { st with calls := ⟨fs, Nat.le_of_succ_le h⟩ }
        | ⟨[], _⟩ => .error "return outside a subroutine"
      else if v == 14 then .ok st
      else if v == 13 then do
        -- hsbw: sbx wx
        let args ← st.stack.bottom 2
        let wx := args.getD 1 Fixed.zero
        run subrs fuel code (pos + 1)
          { st with stack := Stack.empty, sbx := args.getD 0 Fixed.zero,
                    width := some (wx, Fixed.zero) }
      else if v == 1 || v == 3 || (4 ≤ v ∧ v ≤ 9) || v == 21 || v == 22 || v == 30 || v == 31
      then run subrs fuel code (pos + 1) { st with stack := Stack.empty }
      else .error "unknown charstring operator"

/-- The argument stack of any state `run` returns holds at most `maxStack` operands (by
construction: `Stack` carries the bound). -/
theorem run_stack_le {subrs : Array ByteArray} {fuel : Nat} {code : ByteArray} {pos : Nat}
    {st st' : CState} (_h : run subrs fuel code pos st = .ok st') :
    st'.stack.1.length ≤ maxStack := st'.stack.2

/-- Subroutine nesting in any state `run` reaches is at most `maxCallDepth` (by construction). -/
theorem run_calls_le {subrs : Array ByteArray} {fuel : Nat} {code : ByteArray} {pos : Nat}
    {st st' : CState} (_h : run subrs fuel code pos st = .ok st') :
    st'.calls.1.length ≤ maxCallDepth := st'.calls.2

/-- A glyph's metrics in glyph space. -/
structure Glyph where
  /-- The glyph name. -/
  name : String
  /-- Left side bearing. -/
  sbx : Fixed
  /-- Advance width `wx`. -/
  wx : Fixed
  /-- Vertical advance `wy` (0 unless `sbw`). -/
  wy : Fixed
  /-- `seac` accent composition `(base code, accent code)`, if any. -/
  seac : Option (UInt8 × UInt8)
  deriving Repr, Inhabited

/-- Decrypt and run one charstring, at most `glyphFuel` steps. -/
def evalGlyph (subrs : Array ByteArray) (lenIV : Int) (name : String) (enc : ByteArray) :
    Except String Glyph := do
  let st ← run subrs glyphFuel (decryptCharstring lenIV enc) 0 {}
  match st.width with
  | some (wx, wy) => .ok { name, sbx := st.sbx, wx, wy, seac := st.seac }
  | none => .error "no hsbw/sbw"

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

/-- The text-space advance of a glyph with displacement `(wx, wy)` under `/FontMatrix`
entries `a` and `c` (exact decimals): `wx·a + wy·c`, computed exactly and rounded once. -/
def textAdvance (a c : Decimal) (wx wy : Fixed) : Fixed :=
  let pa : Int := ((10 ^ a.scale : Nat) : Int)
  let pc : Int := ((10 ^ c.scale : Nat) : Int)
  Fixed.clamp (roundDiv (wx.raw * a.mantissa * pc + wy.raw * c.mantissa * pa) (pa * pc))

/-- A parsed Type 1 font: what text extraction and glyph positioning need. -/
structure Font1 where
  /-- `/FontName` (empty if absent). -/
  name : String
  /-- `/FontMatrix` (default `[0.001 0 0 0.001 0 0]`). -/
  fontMatrix : Matrix
  /-- The exact `a` entry of `/FontMatrix`. -/
  matrixA : Decimal
  /-- The exact `c` entry of `/FontMatrix`. -/
  matrixC : Decimal
  /-- `/FontBBox` (zeros if absent). -/
  bbox : BBox
  /-- The built-in encoding: code ↦ glyph name (`none` for `.notdef`). -/
  encoding : Array (Option String)
  /-- The encoding has 256 entries. -/
  encoding_size : encoding.size = 256
  /-- Glyphs whose charstring validated, in file order. -/
  glyphs : Array Glyph
  /-- Glyphs whose charstring was rejected, with the reason. -/
  rejected : Array (String × String)
  /-- `/lenIV`. -/
  lenIV : Int
  /-- Precomputed text-space advance per code through the built-in encoding. -/
  advances : Array (Option Fixed)
  /-- `advances` has 256 entries. -/
  advances_size : advances.size = 256

/-- The glyph with a given name (first definition). -/
def Font1.glyph? (f : Font1) (n : String) : Option Glyph := f.glyphs.find? (·.name == n)

/-- The glyph-space advance width of a named glyph. -/
def Font1.widthOf (f : Font1) (n : String) : Option Fixed := (f.glyph? n).map (·.wx)

/-- The text-space advance of `code` through the built-in encoding. -/
def Font1.advance (f : Font1) (code : UInt8) : Option Fixed :=
  (f.advances[code.toNat]?).join

/-- The per-code advance table: code ↦ encoded glyph ↦ text-space advance. -/
def mkAdvances (enc : Array (Option String)) (glyphs : Array Glyph) (a c : Decimal) :
    Array (Option Fixed) :=
  Array.ofFn fun (k : Fin 256) =>
    match enc[k.val]?.join with
    | some n => (glyphs.find? (·.name == n)).map fun g => textAdvance a c g.wx g.wy
    | none => none

/-- `mkAdvances` has 256 entries. -/
theorem mkAdvances_size (enc : Array (Option String)) (glyphs : Array Glyph) (a c : Decimal) :
    (mkAdvances enc glyphs a c).size = 256 := Array.size_ofFn

/-- **Advance spec**: the advance of code `k` is the text-space advance of the glyph the
built-in encoding names for `k`. -/
theorem mkAdvances_get (enc : Array (Option String)) (glyphs : Array Glyph) (a c : Decimal)
    (k : UInt8) : ((mkAdvances enc glyphs a c)[k.toNat]?).join =
      match enc[k.toNat]?.join with
      | some n => (glyphs.find? (·.name == n)).map fun g => textAdvance a c g.wx g.wy
      | none => none := by
  have hk : k.toNat < 256 := k.toNat_lt
  unfold mkAdvances
  rw [Array.getElem?_eq_getElem (by simp only [Array.size_ofFn]; exact hk), Array.getElem_ofFn]
  simp only [Option.join_some]

/-- The default `/FontMatrix` entry `0.001`. -/
def milli : Decimal := ⟨1, 3⟩

/-- Parse an embedded Type 1 font program (`/FontFile` contents, Flate already decoded),
given the stream dictionary's `/Length1` and `/Length2`. Fails only when the program has no
usable structure (no eexec section, no valid charstring) or exceeds a cap; individual bad
charstrings are skipped and listed in `rejected`. -/
def parse (limits : Limits) (bytes : ByteArray) (len1 len2 : Option Nat := none) :
    Except Error Font1 := do
  if limits.maxDecodedStreamBytes < bytes.size then throw (.limitExceeded .decodedStreamBytes)
  let parts ← split bytes len1 len2
  let ci := scanClear (tokenize parts.clear 0 none #[]).toList {}
  let plain := eexecDecrypt parts.cipher
  let pi := scanPrivate (tokenize plain 0 none #[]).toList {}
  if maxGlyphs < pi.charstrings.length then
    throw (.malformed 0 s!"Type 1: more than {maxGlyphs} charstrings")
  if pi.subrs.any (fun (i, _) => maxSubrs ≤ i) then
    throw (.malformed 0 s!"Type 1: subroutine index ≥ {maxSubrs}")
  let nSubrs := pi.subrs.foldl (fun m (i, _) => max m (i + 1)) 0
  let subrs := pi.subrs.reverse.foldl (fun a (i, b) =>
    a.setIfInBounds i (decryptCharstring pi.lenIV b)) (Array.replicate nSubrs ByteArray.empty)
  let (glyphs, rejected) := pi.charstrings.reverse.foldl (fun (gs, rs) (n, b) =>
    match evalGlyph subrs pi.lenIV n b with
    | .ok g => (gs.push g, rs)
    | .error e => (gs, rs.push (n, e))) ((#[] : Array Glyph), (#[] : Array (String × String)))
  if glyphs.isEmpty then throw (.malformed 0 "Type 1: no valid charstring")
  let z : Decimal := ⟨0, 0⟩
  let dm : List Decimal := ci.matrix.getD [milli, z, z, milli, z, z]
  let fx (k : Nat) : Fixed := Fixed.ofDecimal (dm.getD k ⟨0, 0⟩)
  let bb : List Decimal := ci.bbox.getD []
  let bx (k : Nat) : Fixed := Fixed.ofDecimal (bb.getD k ⟨0, 0⟩)
  let encoding := match ci.encKind with
    | .explicit => encodingOf ci.entries.reverse
    | _ => encodingOf standardEncodingEntries
  let a := dm.getD 0 ⟨0, 0⟩
  let c := dm.getD 2 ⟨0, 0⟩
  return {
    name := ci.name.getD ""
    fontMatrix := ⟨fx 0, fx 1, fx 2, fx 3, fx 4, fx 5⟩
    matrixA := a
    matrixC := c
    bbox := ⟨bx 0, bx 1, bx 2, bx 3⟩
    encoding
    encoding_size := by
      simp only [encoding]; split <;> exact encodingOf_size _
    glyphs, rejected
    lenIV := pi.lenIV
    advances := mkAdvances encoding glyphs a c
    advances_size := mkAdvances_size _ _ _ _ }

/-- **Advance law** of a parsed font: the advance of `code` is the text-space advance of the
glyph its built-in encoding names (when `advances` is built by `mkAdvances`, as `parse`
does). -/
theorem Font1.advance_eq (f : Font1)
    (h : f.advances = mkAdvances f.encoding f.glyphs f.matrixA f.matrixC) (code : UInt8) :
    f.advance code = match f.encoding[code.toNat]?.join with
      | some n => (f.glyph? n).map fun g => textAdvance f.matrixA f.matrixC g.wx g.wy
      | none => none := by
  unfold Font1.advance Font1.glyph?
  rw [h, mkAdvances_get]

/-! ## Tests

The fixture is `Tests/fonts/tiny.t1` without its trailer, generated by
`python3 -I Tests/fonts/gen_type1.py` (`/Length1 568`, `/Length2 696`): FontName
`SafePdfTiny`, five charstrings `.notdef` 500, `space` 250, `A` 600, `B` 650 (via `div` and
`callsubr`), `C` 700 (`seac` of `A` and `B`), explicit encoding 32/65/66/67. -/

/-- Decodes a hex string (whitespace ignored); test helper. -/
private def fromHex (str : String) : ByteArray := hexDecode str.toUTF8

/-- Lower-case hex of a byte string with a newline every 32 bytes; test helper. -/
private def toHex (b : ByteArray) : ByteArray := Id.run do
  let digit (v : UInt8) : UInt8 := if v < 10 then 48 + v else 87 + v
  let mut out := ByteArray.empty
  for k in [0:b.size] do
    let v := b[k]?.getD 0
    out := (out.push (digit (v / 16))).push (digit (v % 16))
    if k % 32 == 31 then out := out.push 10
  return out

/-- The fixture font program (clear text and binary eexec section). -/
private def tinyT1 : ByteArray := fromHex
  "252150532d41646f6265466f6e742d312e303a205361666550646654696e79203030312e3030300a252543726561
  74696f6e446174653a2067656e6572617465642062792054657374732f666f6e74732f67656e5f74797065312e70
  790a3131206469637420626567696e0a2f466f6e74496e666f203220646963742064757020626567696e0a2f4e6f
  7469636520285465737420666f6e7420286329206e6f626f6479205c287075626c696320646f6d61696e5c292920
  726561646f6e6c79206465660a2f46756c6c4e616d652028536166655064662054696e792920726561646f6e6c79
  206465660a656e6420726561646f6e6c79206465660a2f466f6e744e616d65202f5361666550646654696e792064
  65660a2f5061696e74547970652030206465660a2f466f6e74547970652031206465660a2f466f6e744d61747269
  78205b302e3030312030203020302e303031203020305d20726561646f6e6c79206465660a2f456e636f64696e67
  203235362061727261790a30203120323535207b3120696e6465782065786368202f2e6e6f74646566207075747d
  20666f720a647570203332202f7370616365207075740a647570203635202f41207075740a647570203636202f42
  207075740a647570203637202f43207075740a726561646f6e6c79206465660a2f466f6e7442426f78207b2d3130
  202d32302031303030203830307d20726561646f6e6c79206465660a63757272656e746469637420656e640a6375
  7272656e7466696c652065657865630a834c8dfbfbbf9dafe4e5bf45a604f5f3a87e71326d7d918349376bc8515e
  b4561f93d52ba5ceeafe45f7c04a9caa1cdd6e08b8ca634249a0875720d215acdfe39a43b790610b32ae121a12c8
  aabcd6cd8bf26a0f2affc65c1ea7df7f46e84c53e49c14203a3287c8ad8c7692d1d4e2b27ea260b35d6d11d897dc
  19bb5d4a006590e41216ab790858d0756213090f70253fd2ee85da8974084c15954c5d427721b49e49d21efcc870
  45d9fa0d2adeb6c03620ee079fb6668924bc5017487ebfeb3ac0499d83ed13a55bd4745dbf516e7891b01e684d92
  cf54878a39e8a352a6900c7dcbff8c1ab53aceaf9003cc48c1068626f47d39df4ae82104d3dbaed74edbd772d0ca
  e80c6547e95973a14289bfe2575672e1b4dadcdaf5df770eaa606c3a540d2f4f23f6f7ee493b1f7864291a3b3f75
  bdb9763a4a16b98d0af9852614174e7afb633e604b1ead47ecc3e49b1d537e8542c599d4e6bf45fbe586be8bbfe8
  b5f5379d8fcf35704e98a3dc5277003d6f1d46a6ddd51b3c62188c66d7d12ce55bfd2e9f922a4995e08362cfdedd
  94d974ff2702c8bc07e092df244afb5ac6d1e3c5ae933563b02abaf844cd8a2c7369480c0bf926e1f30ef26c729b
  1e121cfac85eec59162f70a1fdeaad5c10bead7e58bf3991101314daebc2e400c84ae362a9d991ba5e7d65fb18bc
  db0a88c10cdd514d18c4c08e161c9a16da891583a75527b93306d45c527c3f1221fe30941d584b04aeef80f7bf0f
  46be9a5c37de68ca029715a835a28f2aa44b7b289c4279f602fc08eb3e82f84e5477af695bc5c28c310f15aea54d
  510ea037b108a04d81faba00fc7313c991a86625055ccb584fd9a27fc8763531933c0024c673a6db96f1bed4d61f
  e2601c6043afe078c8ace700d4ce792d3ff927c63430d31df5fe2119cc983c0a7a0e49cef1de01c236d407427d62
  dd509b436c022e355cef2dcb573188c4b7e02a0d6e08"

/-- The clear-text part of the fixture. -/
private def tinyClear : ByteArray := tinyT1.extract 0 568

/-- The binary eexec part of the fixture. -/
private def tinyBin : ByteArray := tinyT1.extract 568 tinyT1.size

/-- A 4-byte little-endian length; test helper. -/
private def le4 (n : Nat) : ByteArray :=
  ⟨#[n.toUInt8, (n / 256).toUInt8, (n / 65536).toUInt8, (n / 16777216).toUInt8]⟩

/-- The fixture as a PFB file. -/
private def tinyPfb : ByteArray :=
  ByteArray.mk #[0x80, 1] ++ le4 tinyClear.size ++ tinyClear ++ ByteArray.mk #[0x80, 2] ++
    le4 tinyBin.size ++ tinyBin ++ ByteArray.mk #[0x80, 3]

/-- The fixture with a hex eexec section (PFA). -/
private def tinyPfa : ByteArray := tinyClear ++ toHex tinyBin

/-- Summary of a parse: name, widths of all glyphs, advances of codes 32 65 66 67 0, the
rejected count, `seac` of `C`, the bbox and the matrix `a` entry (raw values). -/
private def summary (r : Except Error Font1) :
    Option (String × List (String × Int) × List (Option Int) × Nat × Option (UInt8 × UInt8) ×
      List Int × Int) :=
  match r with
  | .ok f => some (f.name, f.glyphs.toList.map (fun g => (g.name, g.wx.raw)),
      [32, 65, 66, 67, 0].map (fun (c : UInt8) => (f.advance c).map (·.raw)), f.rejected.size,
      (f.glyph? "C").bind (·.seac), [f.bbox.llx.raw, f.bbox.lly.raw, f.bbox.urx.raw,
      f.bbox.ury.raw], f.fontMatrix.a.raw)
  | .error _ => none

/-- The expected summary of the fixture. -/
private def expected :
    Option (String × List (String × Int) × List (Option Int) × Nat × Option (UInt8 × UInt8) ×
      List Int × Int) :=
  some ("SafePdfTiny",
    [(".notdef", 500000000), ("space", 250000000), ("A", 600000000), ("B", 650000000),
     ("C", 700000000)],
    [some 250000, some 600000, some 650000, some 700000, none], 0, some (65, 66),
    [-10000000, -20000000, 1000000000, 800000000], 1000)

#guard tinyT1.size == 568 + 696
-- Length laws and round trip.
#guard (eexecDecrypt tinyBin).size == 692
#guard (decrypt eexecKey 4 (encrypt eexecKey "abcd".toUTF8 "hello".toUTF8)).toList ==
  "hello".toUTF8.toList
#guard (eexecDecrypt ByteArray.empty).size == 0
-- The plaintext of the private part starts as written by the generator.
#guard ((eexecDecrypt tinyBin).extract 0 13).toList == "dup /Private ".toUTF8.toList
-- The fixture with correct, missing and wrong lengths, as PFB and as PFA.
#guard summary (parse Limits.default tinyT1 (some 568) (some 696)) == expected
#guard summary (parse Limits.default tinyT1) == expected
#guard summary (parse Limits.default tinyT1 (some 3) (some 999999)) == expected
#guard summary (parse Limits.default tinyT1 (some 570) (some 10)) == expected
#guard summary (parse Limits.default tinyPfb) == expected
#guard summary (parse Limits.default tinyPfa) == expected
-- Split: the clear text ends right after `eexec` and its newline.
#guard match split tinyT1 none none with
  | .ok p => p.clear.size == 568 && p.cipher.size == 696
  | .error _ => false
-- Garbage and truncated fonts are rejected or degrade cleanly.
#guard (parse Limits.default "not a font".toUTF8).toOption.isNone
#guard (parse Limits.default (tinyT1.extract 0 600)).toOption.isNone
#guard (parse { maxDecodedStreamBytes := 100 } tinyT1).toOption.isNone
-- Cut inside the CharStrings: the glyphs before the cut survive.
#guard match parse Limits.default (tinyT1.extract 0 (568 + 540)) with
  | .ok f => f.glyphs.size < 5 && 0 < f.glyphs.size
  | .error _ => false
-- Tokenizer.
#guard (tokenize "/F 12 -3.5 {x} [ (a(b)c) <0a> << % c\n y".toUTF8 0 none #[]).size == 11
#guard (match nextTok " /Abc def".toUTF8 0 with
  | some (.lit n, j) => n == "Abc" && j == 5
  | _ => false)
#guard (match nextTok "-3.25".toUTF8 0 with
  | some (.real d, _) => d == ⟨-325, 2⟩
  | _ => false)
-- Charstring interpreter (unencrypted, `lenIV = -1`).
#guard (evalGlyph #[] (-1) "g" ⟨#[139, 248, 136, 13, 14]⟩).toOption.map (·.wx.raw) ==
  some 500000000
-- 25 operands overflow the stack of 24.
#guard (evalGlyph #[] (-1) "g" ⟨(Array.replicate 25 139).push 14⟩).toOption.isNone
-- A subroutine that calls itself exceeds the nesting bound.
#guard (evalGlyph #[⟨#[139, 10]⟩] (-1) "g" ⟨#[139, 10]⟩).toOption.isNone
-- No endchar, unknown operator, no hsbw, division by zero.
#guard (evalGlyph #[] (-1) "g" ⟨#[139, 248, 136, 13]⟩).toOption.isNone
#guard (evalGlyph #[] (-1) "g" ⟨#[0]⟩).toOption.isNone
#guard (evalGlyph #[] (-1) "g" ⟨#[14]⟩).toOption.isNone
#guard (evalGlyph #[] (-1) "g" ⟨#[140, 139, 12, 12, 14]⟩).toOption.isNone
-- `sbw`: sbx sby wx wy.
#guard (evalGlyph #[] (-1) "g" ⟨#[139, 139, 239, 149, 12, 7, 14]⟩).toOption.map
  (fun g => (g.wx.raw, g.wy.raw)) == some (100000000, 10000000)
-- Text-space advance with an exact non-decimal-friendly matrix entry 1/2048.
#guard (textAdvance ⟨48828125, 11⟩ ⟨0, 0⟩ (Fixed.ofInt 1024) Fixed.zero).raw == 500000

end SafePdf.Core.Font.Type1
