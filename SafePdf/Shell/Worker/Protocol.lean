import SafePdf.Core.Limits
import SafePdf.Core.Object
import SafePdf.Core.Doc.Nav
import SafePdf.Core.Raster.Geom
import SafePdf.Core.Doc.OptionalContent

/-!
# Document worker protocol (task 12.2a; Plan.md §6 Phase 12 "Restricted, stoppable document worker")

The wire format between the viewer (client) and the document worker
(`SafePdf.Shell.Worker.Main`, a separate process that receives the document **bytes**, never a
path, and answers over stdin/stdout). Pure, `IO`-free and Tk-free, so that the client side
(the GUI, task 12.2c) and the worker share one definition, and the theorems below hold for
both directions.

**Frames.** Every message is one frame: a 4-byte big-endian payload length, then the payload.
The payload is the message: one tag byte, then its fields. Fields are encoded by small
`Codec`s: LEB128 numbers (at most `maxNatBytes` = 20 bytes, so numbers below `2^140`),
zigzag integers, rationals as numerator and denominator, length-prefixed byte strings and
UTF-8 strings, Booleans as 0/1, options and tagged unions with a tag byte, lists with a count.

**Caps** come from `Limits`: a request payload is at most `requestCap` (`maxInputBytes` + 64,
the document of an `openDoc`), a response payload at most `responseCap` (a
`maxPageSide`² RGBA image plus 1 MiB). A header above the cap is an error before any payload
byte is read (`decodeFrame_tooLong`); a list count above the bytes left is rejected before any
item is decoded; a number longer than 20 bytes is rejected. Every decoder is total and
structurally bounded by the frame: malformed input gives a `DecodeError`, never a crash.

**Theorems** (standard axioms only):
* `Codec.rt` (every codec), `decodeBody_rt`, `request_roundtrip`, `response_roundtrip`:
  `decode (encode m) = .ok m` for every valid message (numbers below `2^140`);
* `decodeFrame_at`, `decodeFrame_encodeFrame`, `request_frame_roundtrip`,
  `response_frame_roundtrip`: framed round trip (within the cap), at any position of a buffer;
* `decodeStream_encodeFrames`, `request_stream`, `response_stream`: a stream of encoded
  messages decodes back to the list;
* `decodeFrame_prefix`, `request_prefix`, `response_prefix`: a strict prefix of a frame is
  `incomplete`, never a complete message;
* `decodeFrame_tooLong`, `decodeFrame_next_le`, `frame_bounded`: bounded message sizes;
* task 12.2d: the requests `render` (now with a layers state), `pageIndex` (the viewer's
  selection/search index: cells with text, separator, page-space box and line; line
  directions; hidden flags) and `viewLinks` (the viewer's links, `Action`), and their
  responses, are covered by the same round-trip and framing theorems (their codecs carry
  `rt`); the startup configuration (`StartConfig`, command-line flags) carries the limits as
  hexadecimal `limitsC` bytes: `hexDec_hexEnc`, `limitsOfHex_limitsHex` (round trip).

The proofs track one invariant, `At bs p e` (the bytes `e` occur in `bs` at `p`); every
combinator (`pair`, `iso`, `sigma`, `list`, …) carries its round trip, so a message type's
round trip is the combinator's field.
-/

namespace SafePdf.Shell.Worker.Protocol

open SafePdf SafePdf.Core

/-- Why a byte string does not decode. -/
inductive DecodeError where
  /-- The input ends inside a field starting at `pos`. -/
  | truncated (pos : Nat)
  /-- Unknown tag `tag` before position `pos`. -/
  | badTag (pos : Nat) (tag : Nat)
  /-- An out-of-range value at `pos` (over-long number, zero denominator, bad UTF-8, a list
  count above the bytes left, a Boolean other than 0/1). -/
  | badValue (pos : Nat)
  /-- A frame header announces `len` bytes, above the cap `cap`. -/
  | tooLong (len cap : Nat)
  /-- The message ends at `pos`, before the end of its frame. -/
  | trailing (pos : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- A decoder: bytes and a start position to a value and the position after it. -/
abbrev Dec (α : Type) := ByteArray → Nat → Except DecodeError (α × Nat)

/-- `e` occurs in `bs` at position `p` (the invariant of every round-trip proof). -/
def At (bs : ByteArray) (p : Nat) (e : ByteArray) : Prop :=
  p ≤ bs.size ∧ ∃ r, bs.data.toList.drop p = e.data.toList ++ r

/-- A byte array's size is its byte list's length. -/
theorem size_eq_length (b : ByteArray) : b.size = b.data.toList.length := by
  simp [ByteArray.size_data]

/-- Splitting an occurrence of `a ++ b`. -/
theorem At.append {bs : ByteArray} {p : Nat} {a b : ByteArray} (h : At bs p (a ++ b)) :
    At bs p a ∧ At bs (p + a.size) b := by
  obtain ⟨hp, r, hr⟩ := h
  have hp' := hp
  rw [size_eq_length bs] at hp'
  simp only [ByteArray.data_append, Array.toList_append, List.append_assoc] at hr
  have hl := congrArg List.length hr
  simp only [List.length_drop, List.length_append] at hl
  refine ⟨⟨hp, _, hr⟩, ⟨?_, r, ?_⟩⟩
  · rw [size_eq_length bs, size_eq_length a]; omega
  · rw [← List.drop_drop, hr, size_eq_length, List.drop_left]

/-- An occurring single byte is the byte at `p`. -/
theorem At.byte {bs : ByteArray} {p : Nat} {b : UInt8} (h : At bs p ⟨#[b]⟩) :
    ∃ hp : p < bs.size, bs[p] = b := by
  obtain ⟨_, r, hr⟩ := h
  have h1 : bs.data.toList[p]? = some b := by
    rw [← List.head?_drop, hr]; rfl
  rw [Array.getElem?_toList] at h1
  have hp : p < bs.size := by
    rw [← ByteArray.size_data]
    exact (Array.getElem?_eq_some_iff.mp h1).1
  refine ⟨hp, ?_⟩
  have : bs[p]? = some b := h1
  rw [getElem?_pos bs p hp] at this
  exact Option.some.inj this

/-- An occurrence lies inside the buffer. -/
theorem At.le {bs : ByteArray} {p : Nat} {e : ByteArray} (h : At bs p e) :
    p + e.size ≤ bs.size := by
  obtain ⟨hp, r, hr⟩ := h
  have := congrArg List.length hr
  rw [size_eq_length bs] at hp
  simp only [List.length_drop, List.length_append] at this
  rw [size_eq_length bs, size_eq_length e]
  omega

/-- Extracting an occurrence gives it back. -/
theorem At.extract {bs : ByteArray} {p : Nat} {e : ByteArray} (h : At bs p e) :
    bs.extract p (p + e.size) = e := by
  obtain ⟨_, r, hr⟩ := h
  apply ByteArray.ext
  apply Array.ext'
  rw [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop, hr,
    Nat.add_sub_cancel_left, size_eq_length, List.take_left]

/-- `e` occurs in `a ++ e ++ c` right after `a`. -/
theorem At.ofAppend (a e c : ByteArray) : At (a ++ e ++ c) a.size e :=
  ⟨by simp [ByteArray.size_append]; omega, c.data.toList, by
    simp only [ByteArray.data_append, Array.toList_append, List.append_assoc,
      size_eq_length]
    exact List.drop_left⟩

/-- Bytes of an occurrence, by index. -/
theorem At.getElem? {bs : ByteArray} {p : Nat} {e : ByteArray} (h : At bs p e) {i : Nat}
    (hi : i < e.size) : bs[p + i]? = e[i]? := by
  obtain ⟨_, r, hr⟩ := h
  have h1 : (bs.data.toList.drop p)[i]? = (e.data.toList ++ r)[i]? := by rw [hr]
  rw [List.getElem?_drop, List.getElem?_append_left (by rw [← size_eq_length]; exact hi),
    Array.getElem?_toList, Array.getElem?_toList] at h1
  exact h1

/-- **A codec**: an encoder, a decoder, a validity check (numbers in range) and the proof
that the decoder reads back every valid value wherever its encoding occurs. -/
structure Codec (α : Type) where
  /-- Encoder. -/
  enc : α → ByteArray
  /-- Decoder. -/
  dec : Dec α
  /-- Encodable values (numbers below `2^140`). -/
  valid : α → Bool
  /-- **Round trip**: a valid value decodes from any occurrence of its encoding. -/
  rt : ∀ x bs p, valid x = true → At bs p (enc x) → dec bs p = .ok (x, p + (enc x).size)

namespace Codec

/-- One byte. -/
def u8 : Codec UInt8 where
  enc b := ⟨#[b]⟩
  dec bs p := if h : p < bs.size then .ok (bs[p], p + 1) else .error (.truncated p)
  valid _ := true
  rt x bs p _ h := by
    obtain ⟨hp, hb⟩ := h.byte
    simp [hp, hb] <;> rfl

/-- Nothing (zero bytes). -/
def unit : Codec Unit where
  enc _ := .empty
  dec _ p := .ok ((), p)
  valid _ := true
  rt _ _ _ _ _ := by simp

/-- Two values one after the other. -/
def pair {α β : Type} (ca : Codec α) (cb : Codec β) : Codec (α × β) where
  enc x := ca.enc x.1 ++ cb.enc x.2
  dec bs p := match ca.dec bs p with
    | .error e => .error e
    | .ok (a, q) => match cb.dec bs q with
      | .error e => .error e
      | .ok (b, r) => .ok ((a, b), r)
  valid x := ca.valid x.1 && cb.valid x.2
  rt x bs p hv h := by
    obtain ⟨h1, h2⟩ := h.append
    simp only [Bool.and_eq_true] at hv
    simp only [ca.rt _ _ _ hv.1 h1, cb.rt _ _ _ hv.2 h2]
    simp [ByteArray.size_append, Nat.add_assoc]

/-- A codec through an encoding `f` and a partial inverse `g` (`none`: `badValue`). -/
def partialIso {α β : Type} (c : Codec β) (f : α → β) (g : β → Option α)
    (hg : ∀ a, g (f a) = some a) : Codec α where
  enc a := c.enc (f a)
  dec bs p := match c.dec bs p with
    | .error e => .error e
    | .ok (b, q) => match g b with
      | some a => .ok (a, q)
      | none => .error (.badValue p)
  valid a := c.valid (f a)
  rt a bs p hv h := by
    rw [c.rt _ _ _ hv h]
    simp [hg]

/-- A codec through `f` with a left inverse `g` (`g ∘ f = id`). -/
def iso {α β : Type} (c : Codec β) (f : α → β) (g : β → α) (hg : ∀ a, g (f a) = a) : Codec α :=
  partialIso c f (fun b => some (g b)) (fun a => by simp [hg])

/-- LEB128. -/
def encNat (n : Nat) : ByteArray :=
  if n < 128 then ⟨#[n.toUInt8]⟩ else ⟨#[(n % 128 + 128).toUInt8]⟩ ++ encNat (n / 128)
termination_by n
decreasing_by omega

/-- At most this many LEB128 bytes per number (numbers below `2^140`), so decoding a number costs at most 20 steps. -/
def maxNatBytes : Nat := 20

/-- Decode LEB128 with at most `fuel` bytes. -/
def decNatAux : Nat → ByteArray → Nat → Except DecodeError (Nat × Nat)
  | 0, _, p => .error (.badValue p)
  | fuel + 1, bs, p =>
    if h : p < bs.size then
      let b := bs[p]
      if b < 128 then .ok (b.toNat, p + 1)
      else match decNatAux fuel bs (p + 1) with
        | .error e => .error e
        | .ok (n, q) => .ok (b.toNat - 128 + 128 * n, q)
    else .error (.truncated p)

/-- `Nat.toUInt8` is exact below 256. -/
theorem toUInt8_toNat {n : Nat} (h : n < 256) : n.toUInt8.toNat = n := by
  simp [Nat.toUInt8, UInt8.toNat_ofNat']; omega

/-- LEB128 round trip. -/
theorem decNatAux_rt : ∀ (fuel n : Nat) (bs : ByteArray) (p : Nat), n < 2 ^ (7 * (fuel + 1)) →
    At bs p (encNat n) → decNatAux (fuel + 1) bs p = .ok (n, p + (encNat n).size)
  | fuel, n, bs, p, hn, h => by
    rw [encNat] at h ⊢
    by_cases h128 : n < 128
    · simp only [h128, ite_true] at h ⊢
      obtain ⟨hp, hb⟩ := h.byte
      have hlt : n.toUInt8 < 128 := by
        rw [UInt8.lt_iff_toNat_lt, toUInt8_toNat (by omega)]; simpa using h128
      simp [decNatAux, hp, hb, hlt, toUInt8_toNat (show n < 256 by omega)] <;> rfl
    · simp only [h128, ite_false] at h ⊢
      obtain ⟨h1, h2⟩ := h.append
      obtain ⟨hp, hb⟩ := h1.byte
      have hsz : (⟨#[(n % 128 + 128).toUInt8]⟩ : ByteArray).size = 1 := rfl
      rw [hsz] at h2
      have hlt : ¬ (n % 128 + 128).toUInt8 < 128 := by
        rw [UInt8.lt_iff_toNat_lt, toUInt8_toNat (by omega)]; simp
      cases fuel with
      | zero => simp at hn <;> omega
      | succ fuel =>
      have hn' : n / 128 < 2 ^ (7 * (fuel + 1)) := by
        have : 2 ^ (7 * (fuel + 1 + 1)) = 2 ^ (7 * (fuel + 1)) * 128 := by
          rw [show 7 * (fuel + 1 + 1) = 7 * (fuel + 1) + 7 by omega, Nat.pow_add]
        rw [this] at hn
        exact (Nat.div_lt_iff_lt_mul (by decide)).mpr hn
      have ih := decNatAux_rt fuel (n / 128) bs (p + 1) hn' h2
      rw [decNatAux]
      simp only [hp, ↓reduceDIte, hb, hlt, ite_false, ih]
      rw [toUInt8_toNat (by omega), ByteArray.size_append, hsz]
      simp only [Except.ok.injEq, Prod.mk.injEq]
      omega

/-- A natural number below `2^140`, LEB128. -/
def nat : Codec Nat where
  enc := encNat
  dec := decNatAux maxNatBytes
  valid n := decide (n < 2 ^ (7 * maxNatBytes))
  rt n bs p hv h := decNatAux_rt (maxNatBytes - 1) n bs p (by
    have : maxNatBytes - 1 + 1 = maxNatBytes := rfl
    rw [this]; simpa using hv) h


/-- A byte string: its length, then the bytes (copied out with `extract`). -/
def bytes : Codec ByteArray where
  enc b := encNat b.size ++ b
  dec bs p := match nat.dec bs p with
    | .error e => .error e
    | .ok (n, q) => if q + n ≤ bs.size then .ok (bs.extract q (q + n), q + n)
      else .error (.truncated q)
  valid b := nat.valid b.size
  rt b bs p hv h := by
    obtain ⟨h1, h2⟩ := h.append
    have hn := nat.rt _ _ _ hv h1
    simp only [nat] at hn
    simp only [nat, hn, h2.le, ↓reduceIte]
    rw [h2.extract, ByteArray.size_append, Nat.add_assoc]

/-- No value: decoding reports the unknown tag `t`. -/
def reject (t : Nat) : Codec Empty where
  enc x := x.elim
  dec _ p := .error (.badTag p t)
  valid x := x.elim
  rt x := x.elim

/-- A tagged union: one tag byte `t`, then the payload in codec `cs t`. -/
def sigma {β : Nat → Type} (cs : (t : Nat) → Codec (β t)) : Codec ((t : Nat) × β t) where
  enc x := ⟨#[x.1.toUInt8]⟩ ++ (cs x.1).enc x.2
  dec bs p := if h : p < bs.size then
      ((cs bs[p].toNat).dec bs (p + 1)).map fun yq => (⟨bs[p].toNat, yq.1⟩, yq.2)
    else .error (.truncated p)
  valid x := decide (x.1 < 256) && (cs x.1).valid x.2
  rt x bs p hv h := by
    obtain ⟨t, y⟩ := x
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨h1, h2⟩ := h.append
    obtain ⟨hp, hb⟩ := h1.byte
    have ht : bs[p].toNat = t := by rw [hb]; exact toUInt8_toNat hv.1
    have hsz : (⟨#[t.toUInt8]⟩ : ByteArray).size = 1 := rfl
    rw [hsz] at h2
    simp only [hp, ↓reduceDIte]
    generalize bs[p].toNat = t' at ht ⊢
    subst ht
    rw [(cs t').rt _ _ _ hv.2 h2]
    simp only [Except.map, ByteArray.size_append, hsz, Except.ok.injEq, Prod.mk.injEq, true_and]
    omega

/-- A Boolean as one byte 0/1 (other bytes: `badValue`). -/
def bool : Codec Bool :=
  partialIso u8 (fun b => if b then 1 else 0)
    (fun x => if x = 0 then some false else if x = 1 then some true else none)
    (fun b => by cases b <;> decide)

/-- Zigzag mapping of integers to naturals (0, -1, 1, -2, … ↦ 0, 1, 2, 3, …). -/
def zigzag (i : Int) : Nat := if 0 ≤ i then 2 * i.toNat else 2 * (-i).toNat - 1

/-- The inverse of `zigzag`. -/
def unzigzag (n : Nat) : Int := if n % 2 = 0 then ((n / 2 : Nat) : Int) else -(((n + 1) / 2 : Nat) : Int)

/-- `unzigzag` inverts `zigzag`. -/
theorem unzigzag_zigzag (i : Int) : unzigzag (zigzag i) = i := by
  unfold zigzag unzigzag
  split <;> split <;> omega

/-- An integer, zigzag then LEB128. -/
def int : Codec Int := iso nat zigzag unzigzag unzigzag_zigzag

/-- A rational as numerator and denominator; a zero denominator is `badValue` (the result is normalised by `mkRat`). -/
def rat : Codec Rat :=
  partialIso (pair int nat) (fun q => (q.num, q.den))
    (fun x => if x.2 = 0 then none else some (mkRat x.1 x.2))
    (fun q => by simp [q.den_nz, Rat.mkRat_self])

/-- A string as UTF-8 bytes; invalid UTF-8 is `badValue`. -/
def string : Codec String :=
  partialIso bytes String.toUTF8 String.fromUTF8?
    (fun s => by
      have h : s.toByteArray.IsValidUTF8 := s.isValidUTF8
      simp [String.fromUTF8?, h])

/-- The payload types of `option`. -/
def OptionP (α : Type) : Nat → Type
  | 0 => Unit
  | 1 => α
  | _ => Empty

/-- The payload codecs of `option`. -/
def optionCs {α : Type} (c : Codec α) : (t : Nat) → Codec (OptionP α t)
  | 0 => unit
  | 1 => c
  | t + 2 => reject (t + 2)

/-- An optional value: tag 0 (none) or 1 then the value. -/
def option {α : Type} (c : Codec α) : Codec (Option α) :=
  iso (sigma (optionCs c))
    (fun | none => ⟨0, ()⟩ | some a => ⟨1, a⟩)
    (fun | ⟨0, _⟩ => none | ⟨1, a⟩ => some a | ⟨_ + 2, e⟩ => e.elim)
    (fun o => by cases o <;> rfl)

/-- The items of a list, one after the other (the specification of `encList`). -/
def encItems {α : Type} (c : Codec α) : List α → ByteArray
  | [] => .empty
  | x :: xs => c.enc x ++ encItems c xs

/-- The fast item encoder (`foldl`) is the specification. -/
theorem foldl_encItems {α : Type} (c : Codec α) (xs : List α) (init : ByteArray) :
    xs.foldl (fun acc x => acc ++ c.enc x) init = init ++ encItems c xs := by
  induction xs generalizing init with
  | nil => simp [encItems]
  | cons x xs ih => rw [List.foldl_cons, ih, encItems, ByteArray.append_assoc]

/-- Decode `n` items, accumulating them in reverse. -/
def decItems {α : Type} (c : Codec α) : Nat → ByteArray → Nat → List α →
    Except DecodeError (List α × Nat)
  | 0, _, p, acc => .ok (acc.reverse, p)
  | n + 1, bs, p, acc =>
    match c.dec bs p with
    | .error e => .error e
    | .ok (x, q) => decItems c n bs q (x :: acc)

/-- Items round trip. -/
theorem decItems_rt {α : Type} (c : Codec α) (bs : ByteArray) :
    ∀ (xs acc : List α) (p : Nat), xs.all c.valid = true → At bs p (encItems c xs) →
      decItems c xs.length bs p acc = .ok (acc.reverse ++ xs, p + (encItems c xs).size)
  | [], acc, p, _, _ => by simp [decItems, encItems]
  | x :: xs, acc, p, hv, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hv
    rw [encItems] at h ⊢
    obtain ⟨h1, h2⟩ := h.append
    simp only [List.length_cons, decItems, c.rt _ _ _ hv.1 h1]
    rw [decItems_rt c bs xs (x :: acc) _ hv.2 h2]
    simp [ByteArray.size_append, Nat.add_assoc]

/-- Non-empty items: no more items than bytes. -/
theorem length_le_encItems {α : Type} (c : Codec α) (hne : ∀ x, 0 < (c.enc x).size) :
    ∀ xs : List α, xs.length ≤ (encItems c xs).size
  | [] => by simp
  | x :: xs => by
    have := hne x
    have := length_le_encItems c hne xs
    simp only [List.length_cons, encItems, ByteArray.size_append]
    omega

/-- A list: its length, then its items. Items must encode to at least one byte (`hne`), so
that a count larger than the bytes left is rejected before any item is decoded. -/
def list {α : Type} (c : Codec α) (hne : ∀ x, 0 < (c.enc x).size) : Codec (List α) where
  enc xs := xs.foldl (fun acc x => acc ++ c.enc x) (encNat xs.length)
  dec bs p := match nat.dec bs p with
    | .error e => .error e
    | .ok (n, q) => if n ≤ bs.size - q then decItems c n bs q [] else .error (.badValue p)
  valid xs := nat.valid xs.length && xs.all c.valid
  rt xs bs p hv h := by
    simp only [Bool.and_eq_true] at hv
    rw [foldl_encItems] at h ⊢
    obtain ⟨h1, h2⟩ := h.append
    have hn := nat.rt _ _ _ hv.1 h1
    have hle := h2.le
    have hl := length_le_encItems c hne xs
    simp only [nat] at hn
    have hc : xs.length ≤ bs.size - (p + (encNat xs.length).size) := by omega
    simp only [nat, hn, hc, ↓reduceIte]
    rw [decItems_rt c bs xs [] _ hv.2 h2]
    simp [ByteArray.size_append, Nat.add_assoc]

/-- A one-byte array has size 1. -/
@[simp] theorem size_single (b : UInt8) : (⟨#[b]⟩ : ByteArray).size = 1 := rfl

/-- Bytes encode non-empty. -/
theorem u8_ne (x : UInt8) : 0 < (u8.enc x).size := by simp [u8]

/-- Numbers encode non-empty. -/
theorem nat_ne (n : Nat) : 0 < (nat.enc n).size := by
  simp only [nat]; rw [encNat]; split
  · simp
  · simp [ByteArray.size_append]; omega

/-- Tagged values encode non-empty (the tag). -/
theorem sigma_ne {β : Nat → Type} (cs : (t : Nat) → Codec (β t)) (x : (t : Nat) × β t) :
    0 < ((sigma cs).enc x).size := by
  simp [sigma, ByteArray.size_append, size_single]; omega

/-- A pair is non-empty when its first component is. -/
theorem pair_ne_left {α β : Type} (ca : Codec α) (cb : Codec β) (h : ∀ x, 0 < (ca.enc x).size)
    (x : α × β) : 0 < ((pair ca cb).enc x).size := by
  have := h x.1
  simp only [pair, ByteArray.size_append]; omega

/-- `partialIso` keeps non-emptiness. -/
theorem partialIso_ne {α β : Type} (c : Codec β) (f : α → β) (g : β → Option α) (hg)
    (h : ∀ x, 0 < (c.enc x).size) (x : α) : 0 < ((partialIso c f g hg).enc x).size := h (f x)

/-- `iso` keeps non-emptiness. -/
theorem iso_ne {α β : Type} (c : Codec β) (f : α → β) (g : β → α) (hg)
    (h : ∀ x, 0 < (c.enc x).size) (x : α) : 0 < ((iso c f g hg).enc x).size := h (f x)

end Codec

/-! ## Frames -/

/-- The 4-byte big-endian length header of a frame (`len < 2^32`). -/
def header (len : Nat) : ByteArray :=
  ⟨#[(len / 16777216 % 256).toUInt8, (len / 65536 % 256).toUInt8, (len / 256 % 256).toUInt8,
    (len % 256).toUInt8]⟩

/-- The length in the 4-byte header at `p`, `none` when fewer than 4 bytes are left. -/
def readHeader (bs : ByteArray) (p : Nat) : Option Nat :=
  if h : p + 4 ≤ bs.size then
    some (bs[p].toNat * 16777216 + bs[p + 1].toNat * 65536 + bs[p + 2].toNat * 256 +
      bs[p + 3].toNat)
  else none

/-- A frame: the header, then the message. -/
def encodeFrame {α : Type} (c : Codec α) (m : α) : ByteArray :=
  let body := c.enc m
  header body.size ++ body

/-- The result of decoding one frame from a buffer. -/
inductive Frame (α : Type) where
  /-- A complete message; the next frame starts at `next`. -/
  | ok (m : α) (next : Nat)
  /-- The buffer ends inside the frame (more bytes may complete it). -/
  | incomplete
  /-- The frame is malformed or longer than the cap. -/
  | error (e : DecodeError)

/-- Decode a whole message body: the codec must consume every byte. -/
def decodeBody {α : Type} (c : Codec α) (body : ByteArray) : Except DecodeError α :=
  match c.dec body 0 with
  | .error e => .error e
  | .ok (m, q) => if q = body.size then .ok m else .error (.trailing q)

/-- Decode the frame at `p` with a payload cap of `cap` bytes. -/
def decodeFrame {α : Type} (c : Codec α) (cap : Nat) (bs : ByteArray) (p : Nat) : Frame α :=
  match readHeader bs p with
  | none => .incomplete
  | some len =>
    if cap < len then .error (.tooLong len cap)
    else if bs.size < p + 4 + len then .incomplete
    else match decodeBody c (bs.extract (p + 4) (p + 4 + len)) with
      | .ok m => .ok m (p + 4 + len)
      | .error e => .error e

/-- **Round trip**: a valid message decodes from its encoding. -/
theorem decodeBody_rt {α : Type} (c : Codec α) (m : α) (hv : c.valid m = true) :
    decodeBody c (c.enc m) = .ok m := by
  have h : At (c.enc m) 0 (c.enc m) := ⟨Nat.zero_le _, [], by simp⟩
  simp [decodeBody, c.rt _ _ _ hv h]

/-- Bytes of an occurrence, by index (with bounds). -/
theorem At.getElem {bs : ByteArray} {p : Nat} {e : ByteArray} (h : At bs p e) (i : Nat)
    (hi : i < e.size) (hb : p + i < bs.size) : bs[p + i] = e[i] := by
  have := At.getElem? h hi
  rw [getElem?_pos bs _ hb, getElem?_pos e _ hi] at this
  exact Option.some.inj this

/-- The header of a length below `2^32` reads back. -/
theorem readHeader_at {bs : ByteArray} {p len : Nat} (hl : len < 2 ^ 32)
    (h : At bs p (header len)) : readHeader bs p = some len := by
  have hle := h.le
  have hs : (header len).size = 4 := rfl
  rw [hs] at hle
  simp only [readHeader, hle, ↓reduceDIte, Option.some.injEq]
  have e0 := At.getElem h 0 (by rw [hs]; decide) (by omega)
  have e1 := At.getElem h 1 (by rw [hs]; decide) (by omega)
  have e2 := At.getElem h 2 (by rw [hs]; decide) (by omega)
  have e3 := At.getElem h 3 (by rw [hs]; decide) (by omega)
  simp only [Nat.add_zero] at e0
  rw [e0, e1, e2, e3]
  simp only [header, ByteArray.getElem_eq_getElem_data, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  rw [Codec.toUInt8_toNat (by omega), Codec.toUInt8_toNat (by omega), Codec.toUInt8_toNat (by omega),
    Codec.toUInt8_toNat (by omega)]
  omega

/-- A header is 4 bytes. -/
theorem size_header (len : Nat) : (header len).size = 4 := rfl

/-- **Framed round trip at any position**: a frame occurring at `p` decodes to its message, and the next frame starts right after it. -/
theorem decodeFrame_at {α : Type} (c : Codec α) {cap : Nat} {m : α} {bs : ByteArray} {p : Nat}
    (hv : c.valid m = true) (hcap : (c.enc m).size ≤ cap) (hcap32 : cap < 2 ^ 32)
    (h : At bs p (encodeFrame c m)) :
    decodeFrame c cap bs p = .ok m (p + (encodeFrame c m).size) := by
  simp only [encodeFrame] at h ⊢
  obtain ⟨h1, h2⟩ := h.append
  rw [size_header] at h2
  have hle := h2.le
  have hn : ¬ bs.size < p + 4 + (c.enc m).size := by omega
  simp only [decodeFrame, readHeader_at (Nat.lt_of_le_of_lt hcap hcap32) h1,
    Nat.not_lt.mpr hcap, ↓reduceIte, hn, h2.extract, decodeBody_rt c m hv]
  simp only [ByteArray.size_append, size_header, Nat.add_assoc]

/-- **Framed round trip**. -/
theorem decodeFrame_encodeFrame {α : Type} (c : Codec α) {cap : Nat} {m : α}
    (hv : c.valid m = true) (hcap : (c.enc m).size ≤ cap) (hcap32 : cap < 2 ^ 32) :
    decodeFrame c cap (encodeFrame c m) 0 = .ok m (encodeFrame c m).size := by
  have h : At (encodeFrame c m) 0 (encodeFrame c m) := ⟨Nat.zero_le _, [], by simp⟩
  rw [decodeFrame_at c hv hcap hcap32 h, Nat.zero_add]

/-- **Bounded**: a header above the cap is an error (the payload is neither awaited nor read). -/
theorem decodeFrame_tooLong {α : Type} (c : Codec α) {cap len : Nat} {bs : ByteArray} {p : Nat}
    (h : readHeader bs p = some len) (hl : cap < len) :
    decodeFrame c cap bs p = .error (.tooLong len cap) := by
  simp [decodeFrame, h, hl]

/-- A decoded frame ends inside the buffer and at most `4 + cap` bytes after its start. -/
theorem decodeFrame_next_le {α : Type} (c : Codec α) {cap : Nat} {bs : ByteArray} {p q : Nat}
    {m : α} (h : decodeFrame c cap bs p = .ok m q) : q ≤ p + 4 + cap ∧ q ≤ bs.size := by
  unfold decodeFrame at h
  split at h
  · cases h
  · rename_i len _
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h; omega
        · cases h

/-- Concatenated frames (specification). -/
def framesSpec {α : Type} (c : Codec α) : List α → ByteArray
  | [] => .empty
  | m :: ms => encodeFrame c m ++ framesSpec c ms

/-- Concatenated frames. -/
def encodeFrames {α : Type} (c : Codec α) (ms : List α) : ByteArray :=
  ms.foldl (fun acc m => acc ++ encodeFrame c m) .empty

/-- The fast concatenation is the specification. -/
theorem encodeFrames_eq {α : Type} (c : Codec α) (ms : List α) :
    encodeFrames c ms = framesSpec c ms := by
  suffices ∀ init, ms.foldl (fun acc m => acc ++ encodeFrame c m) init = init ++ framesSpec c ms by
    simpa [encodeFrames] using this .empty
  induction ms with
  | nil => simp [framesSpec]
  | cons m ms ih => intro init; rw [List.foldl_cons, ih, framesSpec, ByteArray.append_assoc]

/-- Decode frames from `p` to the end of `bs` (accumulating in reverse). -/
def decodeStreamAux {α : Type} (c : Codec α) (cap : Nat) (bs : ByteArray) :
    Nat → Nat → List α → Except DecodeError (List α)
  | 0, p, _ => .error (.badValue p)
  | fuel + 1, p, acc =>
    if p = bs.size then .ok acc.reverse
    else match decodeFrame c cap bs p with
      | .ok m q => if q ≤ p then .error (.badValue p) else decodeStreamAux c cap bs fuel q (m :: acc)
      | .incomplete => .error (.truncated p)
      | .error e => .error e

/-- Decode a buffer that must hold whole frames only. -/
def decodeStream {α : Type} (c : Codec α) (cap : Nat) (bs : ByteArray) : Except DecodeError (List α) :=
  decodeStreamAux c cap bs (bs.size + 1) 0 []

/-- A frame is the payload plus 4 header bytes. -/
theorem size_encodeFrame {α : Type} (c : Codec α) (m : α) :
    (encodeFrame c m).size = 4 + (c.enc m).size := by
  simp [encodeFrame, ByteArray.size_append, size_header]

/-- No more frames than bytes. -/
theorem length_le_framesSpec {α : Type} (c : Codec α) : ∀ ms : List α, ms.length ≤ (framesSpec c ms).size
  | [] => by simp
  | m :: ms => by
    have := length_le_framesSpec c ms
    simp only [List.length_cons, framesSpec, ByteArray.size_append, size_encodeFrame]
    omega

/-- Stream round trip from any position. -/
theorem decodeStreamAux_rt {α : Type} (c : Codec α) {cap : Nat} (hcap32 : cap < 2 ^ 32)
    (bs : ByteArray) : ∀ (ms : List α) (fuel p : Nat) (acc : List α),
    (∀ m ∈ ms, c.valid m = true ∧ (c.enc m).size ≤ cap) → At bs p (framesSpec c ms) →
    p + (framesSpec c ms).size = bs.size → ms.length < fuel →
    decodeStreamAux c cap bs fuel p acc = .ok (acc.reverse ++ ms)
  | [], fuel + 1, p, acc, _, _, he, _ => by
    simp only [framesSpec] at he
    simp [decodeStreamAux, show p = bs.size by simpa using he]
  | m :: ms, fuel + 1, p, acc, hv, h, he, hf => by
    simp only [framesSpec] at h he
    obtain ⟨h1, h2⟩ := h.append
    have hm := hv m (List.mem_cons_self ..)
    have hsz := size_encodeFrame c m
    rw [ByteArray.size_append] at he
    have hne : ¬ p = bs.size := by omega
    have hq : ¬ p + (encodeFrame c m).size ≤ p := by omega
    simp only [decodeStreamAux, hne, ↓reduceIte, decodeFrame_at c hm.1 hm.2 hcap32 h1, hq]
    rw [decodeStreamAux_rt c hcap32 bs ms fuel _ (m :: acc)
      (fun x hx => hv x (List.mem_cons_of_mem _ hx)) h2 (by omega) (by simp at hf; omega)]
    simp
  | _ :: _, 0, _, _, _, _, _, hf => by simp at hf

/-- **Framing**: a stream of encoded frames decodes back to the list of messages. -/
theorem decodeStream_encodeFrames {α : Type} (c : Codec α) {cap : Nat} (hcap32 : cap < 2 ^ 32)
    (ms : List α) (hv : ∀ m ∈ ms, c.valid m = true ∧ (c.enc m).size ≤ cap) :
    decodeStream c cap (encodeFrames c ms) = .ok ms := by
  rw [encodeFrames_eq]
  have h : At (framesSpec c ms) 0 (framesSpec c ms) := ⟨Nat.zero_le _, [], by simp⟩
  have := length_le_framesSpec c ms
  unfold decodeStream
  simpa using decodeStreamAux_rt c hcap32 _ ms _ 0 [] hv h (by simp) (by omega)

/-- The header depends only on its own 4 bytes. -/
theorem readHeader_extract {bs : ByteArray} {k : Nat} (hk : 4 ≤ k) (hks : k ≤ bs.size) :
    readHeader (bs.extract 0 k) 0 = readHeader bs 0 := by
  have hs : (bs.extract 0 k).size = k := by simp [ByteArray.size_extract]; omega
  simp only [readHeader, hs, Nat.zero_add, show 4 ≤ k from hk, show 4 ≤ bs.size by omega,
    ↓reduceDIte, ByteArray.getElem_extract]

/-- **No early message**: every strict prefix of a frame (within the cap) is `incomplete`, never a decoded message. -/
theorem decodeFrame_prefix {α : Type} (c : Codec α) {cap : Nat} {m : α} {k : Nat}
    (hcap : (c.enc m).size ≤ cap) (hcap32 : cap < 2 ^ 32) (hk : k < (encodeFrame c m).size) :
    decodeFrame c cap ((encodeFrame c m).extract 0 k) 0 = .incomplete := by
  have hs : ((encodeFrame c m).extract 0 k).size = k := by
    simp [ByteArray.size_extract]; omega
  have hsz := size_encodeFrame c m
  by_cases h4 : 4 ≤ k
  · have hh : At (encodeFrame c m) 0 (header (c.enc m).size) :=
      (show At (encodeFrame c m) 0 (encodeFrame c m) from ⟨Nat.zero_le _, [], by simp⟩).append.1
    have hr := readHeader_at (Nat.lt_of_le_of_lt hcap hcap32) hh
    simp only [decodeFrame, readHeader_extract h4 (Nat.le_of_lt hk), hr, Nat.not_lt.mpr hcap,
      ↓reduceIte, hs]
    split
    · rfl
    · omega
  · simp [decodeFrame, readHeader, hs, show ¬ 4 ≤ k from h4]


/-! ## Size caps (from `Limits`) -/

/-- The largest payload a 4-byte header can describe. -/
def frameMax : Nat := 2 ^ 32 - 1

/-- **Request cap**: the largest request payload the worker accepts — the document bytes of
an `openDoc` (`Limits.maxInputBytes`) plus 64 bytes of framing fields, at most `frameMax`. -/
def requestCap (l : Limits) : Nat := min (l.maxInputBytes + 64) frameMax

/-- **Response cap**: the largest response payload the client accepts — an RGBA page image
of `Limits.maxPageSide` pixels square plus 1 MiB, at most `frameMax`. -/
def responseCap (l : Limits) : Nat := min (4 * l.maxPageSide * l.maxPageSide + (1 <<< 20)) frameMax

/-- Both caps fit the 4-byte header. -/
theorem requestCap_lt (l : Limits) : requestCap l < 2 ^ 32 := by
  unfold requestCap frameMax; omega

/-- Both caps fit the 4-byte header. -/
theorem responseCap_lt (l : Limits) : responseCap l < 2 ^ 32 := by
  unfold responseCap frameMax; omega

/-! ## Message payload types -/

open Codec

/-- `Raster.Geom.Pt` as two rationals. -/
def pt : Codec Raster.Geom.Pt :=
  iso (pair rat rat) (fun p => (p.x, p.y)) (fun x => ⟨x.1, x.2⟩) (fun _ => rfl)

/-- `Raster.Geom.Box` as four rationals. -/
def box : Codec Raster.Geom.Box :=
  iso (pair rat (pair rat (pair rat rat))) (fun b => (b.llx, b.lly, b.urx, b.ury))
    (fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩) (fun _ => rfl)

/-- `Decimal` as its mantissa and scale. -/
def decimal : Codec Decimal :=
  iso (pair int nat) (fun d => (d.mantissa, d.scale)) (fun x => ⟨x.1, x.2⟩) (fun _ => rfl)

/-- An optional `Decimal` (a fit argument). -/
abbrev ODec := Option Decimal

/-- The payload of each `Fit` tag. -/
def FitP : Nat → Type
  | 0 => ODec × ODec × ODec
  | 1 => Unit
  | 2 => ODec
  | 3 => ODec
  | 4 => ODec × ODec × ODec × ODec
  | 5 => Unit
  | 6 => ODec
  | 7 => ODec
  | 8 => ByteArray
  | _ => Empty

/-- The payload codec of each `Fit` tag. -/
def fitCs : (t : Nat) → Codec (FitP t)
  | 0 => pair (option decimal) (pair (option decimal) (option decimal))
  | 1 => unit
  | 2 => option decimal
  | 3 => option decimal
  | 4 => pair (option decimal) (pair (option decimal) (pair (option decimal) (option decimal)))
  | 5 => unit
  | 6 => option decimal
  | 7 => option decimal
  | 8 => bytes
  | t + 9 => reject (t + 9)

/-- A fit specification (`Core.Doc.Nav.Fit`) as a tagged payload. -/
def Fit.toSig : Doc.Nav.Fit → (t : Nat) × FitP t
  | .xyz l t z => ⟨0, (l, t, z)⟩
  | .fit => ⟨1, ()⟩
  | .fitH t => ⟨2, t⟩
  | .fitV l => ⟨3, l⟩
  | .fitR l b r t => ⟨4, (l, b, r, t)⟩
  | .fitB => ⟨5, ()⟩
  | .fitBH t => ⟨6, t⟩
  | .fitBV l => ⟨7, l⟩
  | .unknown n => ⟨8, ⟨n.toArray⟩⟩

/-- The inverse of `Fit.toSig`. -/
def Fit.ofSig : (t : Nat) × FitP t → Doc.Nav.Fit
  | ⟨0, (l, t, z)⟩ => .xyz l t z
  | ⟨1, _⟩ => .fit
  | ⟨2, t⟩ => .fitH t
  | ⟨3, l⟩ => .fitV l
  | ⟨4, (l, b, r, t)⟩ => .fitR l b r t
  | ⟨5, _⟩ => .fitB
  | ⟨6, t⟩ => .fitBH t
  | ⟨7, l⟩ => .fitBV l
  | ⟨8, n⟩ => .unknown n.data.toList
  | ⟨_ + 9, e⟩ => e.elim

/-- `Core.Doc.Nav.Fit`. -/
def fit : Codec Doc.Nav.Fit :=
  iso (sigma fitCs) Fit.toSig Fit.ofSig (fun f => by cases f <;> rfl)

/-- Where an outline item or a link leads (`SafePdf.Api.Target`). -/
inductive Target where
  /-- Nothing. -/
  | none
  /-- A page of the document (0-based) with its fit specification. -/
  | page (index : Nat) (fitSpec : Doc.Nav.Fit)
  /-- An explicit destination whose page is not in the document. -/
  | danglingDest (fitSpec : Doc.Nav.Fit)
  /-- A named destination that was not found. -/
  | unresolved (name : String)
  /-- A URI action (never followed). -/
  | uri (uri : String)
  /-- Another action, by its `/S` name (never run). -/
  | action (kind : String)
  deriving DecidableEq, Repr, Inhabited

/-- The payload of each `Target` tag. -/
def TargetP : Nat → Type
  | 0 => Unit
  | 1 => Nat × Doc.Nav.Fit
  | 2 => Doc.Nav.Fit
  | 3 => String
  | 4 => String
  | 5 => String
  | _ => Empty

/-- The payload codec of each `Target` tag. -/
def targetCs : (t : Nat) → Codec (TargetP t)
  | 0 => unit
  | 1 => pair nat fit
  | 2 => fit
  | 3 => string
  | 4 => string
  | 5 => string
  | t + 6 => reject (t + 6)

/-- `Target` as a tagged payload. -/
def Target.toSig : Target → (t : Nat) × TargetP t
  | .none => ⟨0, ()⟩
  | .page i f => ⟨1, (i, f)⟩
  | .danglingDest f => ⟨2, f⟩
  | .unresolved n => ⟨3, n⟩
  | .uri u => ⟨4, u⟩
  | .action k => ⟨5, k⟩

/-- The inverse of `Target.toSig`. -/
def Target.ofSig : (t : Nat) × TargetP t → Target
  | ⟨0, _⟩ => .none
  | ⟨1, (i, f)⟩ => .page i f
  | ⟨2, f⟩ => .danglingDest f
  | ⟨3, n⟩ => .unresolved n
  | ⟨4, u⟩ => .uri u
  | ⟨5, k⟩ => .action k
  | ⟨_ + 6, e⟩ => e.elim

/-- `Target`. -/
def target : Codec Target :=
  iso (sigma targetCs) Target.toSig Target.ofSig (fun x => by cases x <;> rfl)

/-- One extracted glyph (`SafePdf.Api.Glyph`). -/
structure Glyph where
  /-- Unicode text. -/
  text : String
  /-- Origin on the baseline, page space. -/
  origin : Raster.Geom.Pt
  /-- Page-space box. -/
  box : Raster.Geom.Box
  /-- Page-space font size. -/
  fontSize : Rat
  /-- Baseline direction in quarter turns. -/
  dir : Nat
  /-- Whether the glyph paints. -/
  visible : Bool
  /-- Provenance: display-list item. -/
  item : Nat
  /-- Provenance: index within the run. -/
  seq : Nat
  deriving DecidableEq, Repr, Inhabited

/-- `Glyph`. -/
def glyph : Codec Glyph :=
  iso (pair string (pair pt (pair box (pair rat (pair nat (pair bool (pair nat nat)))))))
    (fun g => (g.text, g.origin, g.box, g.fontSize, g.dir, g.visible, g.item, g.seq))
    (fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2.1,
      x.2.2.2.2.2.2.2⟩)
    (fun _ => rfl)

/-- One outline item (`SafePdf.Api.OutlineItem`). -/
structure OutlineItem where
  /-- Title, decoded. -/
  title : String
  /-- Nesting depth. -/
  depth : Nat
  /-- Where it leads. -/
  target : Target
  /-- `/Count`. -/
  count : Option Int
  deriving DecidableEq, Repr, Inhabited

/-- `OutlineItem`. -/
def outlineItem : Codec OutlineItem :=
  iso (pair string (pair nat (pair target (option int))))
    (fun o => (o.title, o.depth, o.target, o.count)) (fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩)
    (fun _ => rfl)

/-- A link of a page (`SafePdf.Api.Link`). -/
structure Link where
  /-- `/Rect`, page space. -/
  rect : Raster.Geom.Box
  /-- Where it leads. -/
  target : Target
  deriving DecidableEq, Repr, Inhabited

/-- `Link`. -/
def link : Codec Link :=
  iso (pair box target) (fun l => (l.rect, l.target)) (fun x => ⟨x.1, x.2⟩) (fun _ => rfl)

theorem bytes_ne (b : ByteArray) : 0 < (bytes.enc b).size := by
  have := nat_ne b.size
  simp only [bytes, ByteArray.size_append]; simp only [nat] at this; omega

theorem string_ne (s : String) : 0 < (string.enc s).size := bytes_ne _

theorem rat_ne (q : Rat) : 0 < (rat.enc q).size :=
  partialIso_ne _ _ _ _ (pair_ne_left _ _ (iso_ne _ _ _ _ nat_ne)) q

theorem glyph_ne (g : Glyph) : 0 < (glyph.enc g).size :=
  iso_ne _ _ _ _ (pair_ne_left _ _ string_ne) g

theorem outlineItem_ne (o : OutlineItem) : 0 < (outlineItem.enc o).size :=
  iso_ne _ _ _ _ (pair_ne_left _ _ string_ne) o

theorem link_ne (l : Link) : 0 < (link.enc l).size :=
  iso_ne _ _ _ _ (pair_ne_left _ _ (iso_ne _ _ _ _ (pair_ne_left _ _ rat_ne))) l

/-! ## Task 12.2d: selection index, viewer links, layers state, limits -/

/-- One cell of a page's selection and search index (`App.Select.Cell`, task 12.2d): a glyph's
text in reading order, the separator the layout puts before it, its page-space box and the
index of its line. -/
structure Cell where
  /-- The glyph's text (`""` for an overprinted duplicate). -/
  text : String
  /-- The separator before it (`""`, a space or a line break). -/
  sep : String
  /-- Page-space box (`Select.glyphBox`). -/
  box : Raster.Geom.Box
  /-- Index of its line. -/
  line : Nat
  deriving DecidableEq, Repr, Inhabited

/-- `Cell`. -/
def cell : Codec Cell :=
  iso (pair string (pair string (pair box nat))) (fun c => (c.text, c.sep, c.box, c.line))
    (fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩) (fun _ => rfl)

/-- Cells encode non-empty. -/
theorem cell_ne (c : Cell) : 0 < (cell.enc c).size :=
  iso_ne _ _ _ _ (pair_ne_left _ _ string_ne) c

/-- Booleans encode non-empty. -/
theorem bool_ne (b : Bool) : 0 < (bool.enc b).size := partialIso_ne _ _ _ _ u8_ne b

/-- What activating a link does, as the viewer sees it (`App.Links.Action`, task 12.2d). -/
inductive Action where
  /-- Jump to page `page` (0-based), optionally to a page-space left edge and top edge. -/
  | goto (page : Nat) (left top : Option Rat)
  /-- A `/URI` action with its address as shown (percent-encoded). -/
  | uri (s : String)
  /-- A destination whose page is not in the document. -/
  | badPage
  /-- A named destination that was not found. -/
  | unresolved (name : String)
  /-- Another action type (never followed). -/
  | other (kind : String)
  /-- No destination or action. -/
  | none
  deriving DecidableEq, Repr, Inhabited

/-- The payload of each `Action` tag. -/
def ActionP : Nat → Type
  | 0 => Nat × Option Rat × Option Rat
  | 1 => String
  | 2 => Unit
  | 3 => String
  | 4 => String
  | 5 => Unit
  | _ => Empty

/-- The payload codec of each `Action` tag. -/
def actionCs : (t : Nat) → Codec (ActionP t)
  | 0 => pair nat (pair (option rat) (option rat))
  | 1 => string
  | 2 => unit
  | 3 => string
  | 4 => string
  | 5 => unit
  | t + 6 => reject (t + 6)

/-- `Action` as a tagged payload. -/
def Action.toSig : Action → (t : Nat) × ActionP t
  | .goto p l t => ⟨0, (p, l, t)⟩
  | .uri s => ⟨1, s⟩
  | .badPage => ⟨2, ()⟩
  | .unresolved n => ⟨3, n⟩
  | .other k => ⟨4, k⟩
  | .none => ⟨5, ()⟩

/-- The inverse of `Action.toSig`. -/
def Action.ofSig : (t : Nat) × ActionP t → Action
  | ⟨0, (p, l, t)⟩ => .goto p l t
  | ⟨1, s⟩ => .uri s
  | ⟨2, _⟩ => .badPage
  | ⟨3, n⟩ => .unresolved n
  | ⟨4, k⟩ => .other k
  | ⟨5, _⟩ => .none
  | ⟨_ + 6, e⟩ => e.elim

/-- `Action`. -/
def action : Codec Action :=
  iso (sigma actionCs) Action.toSig Action.ofSig (fun x => by cases x <;> rfl)

/-- A link of a page as the viewer reads it (`App.Links.Link`, task 12.2d). -/
structure ViewLink where
  /-- `/Rect`, normalized, page space. -/
  box : Raster.Geom.Box
  /-- What clicking it does. -/
  action : Action
  deriving DecidableEq, Repr, Inhabited

/-- `ViewLink`. -/
def viewLink : Codec ViewLink :=
  iso (pair box action) (fun l => (l.box, l.action)) (fun x => ⟨x.1, x.2⟩) (fun _ => rfl)

/-- Viewer links encode non-empty. -/
theorem viewLink_ne (l : ViewLink) : 0 < (viewLink.enc l).size :=
  iso_ne _ _ _ _ (pair_ne_left _ _ (iso_ne _ _ _ _ (pair_ne_left _ _ rat_ne))) l

/-- An optional content group key (object number, generation). -/
def ocKey : Codec (Nat × Nat) := pair nat nat

/-- Keys encode non-empty. -/
theorem ocKey_ne (k : Nat × Nat) : 0 < (ocKey.enc k).size := pair_ne_left _ _ nat_ne k

/-- **A layers state** (`Core.Doc.OptionalContent.State`, task 12.2d): the known groups and the
groups that are OFF. -/
def ocState : Codec Doc.OptionalContent.State :=
  iso (pair (list ocKey ocKey_ne) (list ocKey ocKey_ne)) (fun s => (s.known, s.off))
    (fun x => ⟨x.1, x.2⟩) (fun _ => rfl)

/-- The fields of `Limits`, in declaration order. -/
def Limits.toList (l : Limits) : List Nat :=
  [l.maxInputBytes, l.maxDecodedStreamBytes, l.maxDecodedTotalBytes, l.maxImagePixels,
   l.maxObjectDepth, l.maxObjects, l.maxXObjectDepth, l.maxGStateDepth, l.maxOpsPerPage,
   l.maxRevisions, l.maxRepairFailures, l.maxFilters, l.maxFontGlyphs, l.maxFontSubrs,
   l.glyphFuel, l.maxFormsPerPage, l.maxCFFGlyphs, l.fontFuel, l.maxFontDicts, l.curveSegCap,
   l.coordLimit, l.maxDashSteps, l.arcSegCap, l.maxPageSide, l.clipCacheSize, l.maxMarkedDepth,
   l.maxFormCacheEntries, l.maxFormCacheBytes, l.maxOCGroups, l.maxOCDepth]

/-- `Limits` from its fields (`none` unless there are exactly 30). -/
def Limits.ofList? : List Nat → Option Limits
  | [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20,
     a21, a22, a23, a24, a25, a26, a27, a28, a29, a30] =>
    some ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
      a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30⟩
  | _ => none

/-- **`Limits`** (task 12.2d: the viewer's limits, passed to the worker at startup). -/
def limitsC : Codec Limits :=
  partialIso (list nat nat_ne) Limits.toList Limits.ofList? (fun _ => rfl)

/-! ### Startup arguments (task 12.2d)

The worker reads no environment, and it reads its fonts **before** it confines itself, so its
configuration arrives as command-line flags, parsed before `Sandbox.prepare`:
`--limits=HEX` (the `limitsC` encoding in lower-case hexadecimal), `--no-subst` (no
substitute fonts), `--home=DIR` (search `DIR/Library/Fonts`, as the viewer does for `$HOME`),
`--font-dir=DIR` (repeatable; the viewer's `$SAFEPDF_FONT_DIR` entries, in order) and the
test hook `--test-stall-ms=N`. Task 12.3 adds the worker's resource ceilings
`--mem-limit-mib=N` and `--cpu-limit-s=N` (applied before confinement, `Sandbox.fence`) and
the test hook `--test-spin-ms=N`. -/

/-- A hexadecimal digit (lower case) of `n < 16`. -/
def hexDigit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- The value of a lower-case hexadecimal digit. -/
def hexVal? (c : Char) : Option Nat :=
  if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then some (c.toNat - 48)
  else if 97 ≤ c.toNat ∧ c.toNat ≤ 102 then some (c.toNat - 87) else none

/-- Bytes as hexadecimal digits, two per byte. -/
def hexEnc : List UInt8 → List Char
  | [] => []
  | b :: bs => hexDigit (b.toNat / 16) :: hexDigit (b.toNat % 16) :: hexEnc bs

/-- Hexadecimal digits as bytes (`none`: odd length or a non-digit). -/
def hexDec : List Char → Option (List UInt8)
  | [] => some []
  | [_] => none
  | h :: l :: rest =>
    match hexVal? h, hexVal? l, hexDec rest with
    | some a, some b, some r => some ((a * 16 + b).toUInt8 :: r)
    | _, _, _ => none

/-- Every digit reads back. -/
theorem hexVal_hexDigit : ∀ n : Fin 16, hexVal? (hexDigit n.val) = some n.val := by decide

/-- **Hexadecimal round trip**. -/
theorem hexDec_hexEnc : ∀ bs : List UInt8, hexDec (hexEnc bs) = some bs
  | [] => rfl
  | b :: bs => by
    have h1 := hexVal_hexDigit ⟨b.toNat / 16, by have := b.toNat_lt; omega⟩
    have h2 := hexVal_hexDigit ⟨b.toNat % 16, by omega⟩
    simp only at h1 h2
    simp only [hexEnc, hexDec, h1, h2, hexDec_hexEnc bs]
    have : b.toNat / 16 * 16 + b.toNat % 16 = b.toNat := by omega
    rw [this]
    simp

/-- The `--limits=` value of `l`. -/
def limitsHex (l : Limits) : String := String.ofList (hexEnc (limitsC.enc l).data.toList)

/-- The limits of a `--limits=` value. -/
def limitsOfHex? (s : String) : Option Limits :=
  (hexDec s.toList).bind fun bs => (decodeBody limitsC ⟨bs.toArray⟩).toOption

/-- **Limits round trip** (startup argument): the worker reads back exactly the limits the
client passed (numbers below `2^140`). -/
theorem limitsOfHex_limitsHex (l : Limits) (hv : limitsC.valid l = true) :
    limitsOfHex? (limitsHex l) = some l := by
  simp only [limitsOfHex?, limitsHex, String.toList_ofList, hexDec_hexEnc, Option.bind_some,
    Array.toArray_toList]
  rw [decodeBody_rt limitsC l hv]
  rfl

/-- The worker's startup configuration (task 12.2d). -/
structure StartConfig where
  /-- Limits for parsing, rendering and the frame caps. -/
  limits : Limits := {}
  /-- No substitute fonts (the viewer's `SAFEPDF_SUBST_FONTS=0`). -/
  noSubst : Bool := false
  /-- The home directory whose `Library/Fonts` is searched (the viewer's `$HOME`). -/
  home : Option String := none
  /-- Extra font directories (the viewer's `$SAFEPDF_FONT_DIR`), in order. -/
  fontDirs : List String := []
  /-- Test hook: sleep before each render (ms, capped by the worker). -/
  stallMs : Nat := 0
  /-- Task 12.3: the worker's memory ceiling in MiB (`0`: none), enforced by the operating
  system or a watchdog outside Lean's cost model (`Sandbox.fence`). -/
  memLimitMiB : Nat := 0
  /-- Task 12.3: the CPU time one request may use, in seconds (`0`: none), enforced with
  `RLIMIT_CPU`, re-armed before every request (`Sandbox.fence`). -/
  cpuLimitS : Nat := 0
  /-- Task 12.3, test hook: busy-loop this many ms before each render (capped by the worker),
  to exercise the CPU fence. -/
  spinMs : Nat := 0
  deriving Inhabited

/-- The command-line flags of a configuration. -/
def StartConfig.toArgs (c : StartConfig) : Array String :=
  #[s!"--limits={limitsHex c.limits}"] ++ (if c.noSubst then #["--no-subst"] else #[]) ++
    (c.home.map (fun h => #[s!"--home={h}"])).getD #[] ++
    (c.fontDirs.map (s!"--font-dir={·}")).toArray ++
    (if c.stallMs > 0 then #[s!"--test-stall-ms={c.stallMs}"] else #[]) ++
    (if c.memLimitMiB > 0 then #[s!"--mem-limit-mib={c.memLimitMiB}"] else #[]) ++
    (if c.cpuLimitS > 0 then #[s!"--cpu-limit-s={c.cpuLimitS}"] else #[]) ++
    (if c.spinMs > 0 then #[s!"--test-spin-ms={c.spinMs}"] else #[])

/-- One flag applied to a configuration (`.error`: an argument the worker does not
understand). -/
def StartConfig.applyArg (c : StartConfig) (a : String) : Except String StartConfig :=
  if a == "--no-subst" then .ok { c with noSubst := true }
  else if let some v := a.dropPrefix? "--limits=" then
    match limitsOfHex? v.toString with
    | some l => .ok { c with limits := l }
    | none => .error "bad --limits value"
  else if let some v := a.dropPrefix? "--home=" then .ok { c with home := some v.toString }
  else if let some v := a.dropPrefix? "--font-dir=" then
    .ok { c with fontDirs := c.fontDirs ++ [v.toString] }
  else if let some v := a.dropPrefix? "--test-stall-ms=" then
    match v.toString.toNat? with
    | some n => .ok { c with stallMs := n }
    | none => .error "bad --test-stall-ms value"
  else if let some v := a.dropPrefix? "--mem-limit-mib=" then
    match v.toString.toNat? with
    | some n => .ok { c with memLimitMiB := n }
    | none => .error "bad --mem-limit-mib value"
  else if let some v := a.dropPrefix? "--cpu-limit-s=" then
    match v.toString.toNat? with
    | some n => .ok { c with cpuLimitS := n }
    | none => .error "bad --cpu-limit-s value"
  else if let some v := a.dropPrefix? "--test-spin-ms=" then
    match v.toString.toNat? with
    | some n => .ok { c with spinMs := n }
    | none => .error "bad --test-spin-ms value"
  else .error s!"unknown argument: {a}"

/-- Parse the worker's flags (`.error`: the first argument it does not understand). -/
def StartConfig.ofArgs (args : List String) : Except String StartConfig :=
  args.foldlM StartConfig.applyArg {}

#guard match StartConfig.ofArgs ["--mem-limit-mib=2048", "--cpu-limit-s=60", "--test-spin-ms=5"] with
  | .ok c => c.memLimitMiB == 2048 && c.cpuLimitS == 60 && c.spinMs == 5
  | .error _ => false
#guard match StartConfig.ofArgs ({ memLimitMiB := 7, cpuLimitS := 3 } : StartConfig).toArgs.toList with
  | .ok c => c.memLimitMiB == 7 && c.cpuLimitS == 3 && c.spinMs == 0
  | .error _ => false
#guard (StartConfig.ofArgs ["--mem-limit-mib=x"]).toOption.isNone

/-! ## Requests and responses -/

/-- **A request** from the client (the GUI) to the worker. The worker holds at most one open
document; every request but `openDoc` and `quit` refers to it. -/
inductive Request where
  /-- Open a document from its **bytes** (never a path); `allowRepair := false` is strict
  mode (`SafePdf.Api.OpenOptions`). Answered by `docInfo` or `error`. -/
  | openDoc (bytes : ByteArray) (allowRepair : Bool)
  /-- The open document's page count and flags. Answered by `docInfo`. -/
  | info
  /-- Page `page` (0-based): label and displayed size. Answered by `pageInfo`. -/
  | pageInfo (page : Nat)
  /-- Render page `page` at `zoom` pixels per point with an extra clockwise rotation of
  `rotation` quarter turns, under the layers state `oc` (task 12.2d; `none`: the document's
  default configuration). Answered by `image`. -/
  | render (page : Nat) (zoom : Rat) (rotation : Nat) (oc : Option Doc.OptionalContent.State)
  /-- The text and glyphs of page `page` (with annotation text when `withAnnots`). Answered by
  `text`. -/
  | text (page : Nat) (withAnnots : Bool)
  /-- The outline. Answered by `outline`. -/
  | outline
  /-- The links of page `page`. Answered by `links`. -/
  | links (page : Nat)
  /-- End the worker. Answered by `bye`. -/
  | quit
  /-- Task 12.2d: the selection and search index of page `page` (the viewer's text: page and
  annotations, CropBox and clip filtering, under the layers state `oc`). Answered by
  `pageIndex`. -/
  | pageIndex (page : Nat) (oc : Option Doc.OptionalContent.State)
  /-- Task 12.2d: the links of page `page` as the viewer reads them (`App.Links.pageLinks`).
  Answered by `viewLinks`. -/
  | viewLinks (page : Nat)
  deriving DecidableEq, Inhabited

/-- The payload of each request tag (tag 0 and tags above 10 are invalid). -/
def RequestP : Nat → Type
  | 1 => ByteArray × Bool
  | 2 => Unit
  | 3 => Nat
  | 4 => Nat × Rat × Nat × Option Doc.OptionalContent.State
  | 5 => Nat × Bool
  | 6 => Unit
  | 7 => Nat
  | 8 => Unit
  | 9 => Nat × Option Doc.OptionalContent.State
  | 10 => Nat
  | _ => Empty

/-- The payload codec of each request tag. -/
def requestCs : (t : Nat) → Codec (RequestP t)
  | 0 => reject 0
  | 1 => pair bytes bool
  | 2 => unit
  | 3 => nat
  | 4 => pair nat (pair rat (pair nat (option ocState)))
  | 5 => pair nat bool
  | 6 => unit
  | 7 => nat
  | 8 => unit
  | 9 => pair nat (option ocState)
  | 10 => nat
  | t + 11 => reject (t + 11)

/-- `Request` as a tagged payload. -/
def Request.toSig : Request → (t : Nat) × RequestP t
  | .openDoc b r => ⟨1, (b, r)⟩
  | .info => ⟨2, ()⟩
  | .pageInfo i => ⟨3, i⟩
  | .render i z r oc => ⟨4, (i, z, r, oc)⟩
  | .text i a => ⟨5, (i, a)⟩
  | .outline => ⟨6, ()⟩
  | .links i => ⟨7, i⟩
  | .quit => ⟨8, ()⟩
  | .pageIndex i oc => ⟨9, (i, oc)⟩
  | .viewLinks i => ⟨10, i⟩

/-- The inverse of `Request.toSig`. -/
def Request.ofSig : (t : Nat) × RequestP t → Request
  | ⟨0, e⟩ => e.elim
  | ⟨1, (b, r)⟩ => .openDoc b r
  | ⟨2, _⟩ => .info
  | ⟨3, i⟩ => .pageInfo i
  | ⟨4, (i, z, r, oc)⟩ => .render i z r oc
  | ⟨5, (i, a)⟩ => .text i a
  | ⟨6, _⟩ => .outline
  | ⟨7, i⟩ => .links i
  | ⟨8, _⟩ => .quit
  | ⟨9, (i, oc)⟩ => .pageIndex i oc
  | ⟨10, i⟩ => .viewLinks i
  | ⟨_ + 11, e⟩ => e.elim

/-- **The request codec**: one tag byte, then the fields. -/
def request : Codec Request :=
  iso (sigma requestCs) Request.toSig Request.ofSig (fun x => by cases x <;> rfl)

/-- Error kinds carried by `Response.error`. -/
inductive ErrorKind where
  /-- The request frame did not decode (bad tag, truncated field, trailing bytes …). -/
  | malformed
  /-- The request frame's length is above `requestCap`. -/
  | tooLong
  /-- No document is open. -/
  | noDocument
  /-- The document did not open (`SafePdf.Api.Error`). -/
  | openFailed
  /-- A per-page call failed (page out of range, bad zoom or rotation, core error). -/
  | pageFailed
  /-- The response would exceed `responseCap` (or a field its codec's range). -/
  | responseTooLarge
  deriving DecidableEq, Repr, Inhabited

/-- The wire number of an error kind. -/
def ErrorKind.toNat : ErrorKind → Nat
  | .malformed => 1 | .tooLong => 2 | .noDocument => 3 | .openFailed => 4 | .pageFailed => 5
  | .responseTooLarge => 6

/-- The error kind of a wire number. -/
def ErrorKind.ofNat? : Nat → Option ErrorKind
  | 1 => some .malformed | 2 => some .tooLong | 3 => some .noDocument | 4 => some .openFailed
  | 5 => some .pageFailed | 6 => some .responseTooLarge | _ => none

/-- `ErrorKind`, as its wire number. -/
def errorKind : Codec ErrorKind :=
  partialIso nat ErrorKind.toNat ErrorKind.ofNat? (fun k => by cases k <;> rfl)

/-- **A response** from the worker. -/
inductive Response where
  /-- The open document: page count, opened by the repair path, encrypted. -/
  | docInfo (pages : Nat) (repaired encrypted : Bool)
  /-- A page's label and displayed size in points (CropBox, `/Rotate` applied) and its
  `/Rotate` in quarter turns. -/
  | pageInfo (label : String) (width height : Rat) (rotation : Nat)
  /-- A rendered page: `4 · width · height` RGBA bytes, rows from the top. -/
  | image (width height : Nat) (rgba : ByteArray)
  /-- A page's text in reading order and its glyphs in content order. -/
  | text (text : String) (glyphs : List Glyph)
  /-- The outline in preorder. -/
  | outline (items : List OutlineItem)
  /-- A page's links. -/
  | links (links : List Link)
  /-- The request failed. -/
  | error (kind : ErrorKind) (message : String)
  /-- Answer to `quit`. -/
  | bye
  /-- Task 12.2d: a page's selection index — its cells in reading order, the direction of each
  line and, per cell, whether its glyph is not painted (`App.Select.PageIndex`). -/
  | pageIndex (cells : List Cell) (lineDirs : List Nat) (hidden : List Bool)
  /-- Task 12.2d: a page's links as the viewer reads them. -/
  | viewLinks (links : List ViewLink)
  deriving DecidableEq, Inhabited

/-- The payload of each response tag (tag 0 and tags above 10 are invalid). -/
def ResponseP : Nat → Type
  | 1 => Nat × Bool × Bool
  | 2 => String × Rat × Rat × Nat
  | 3 => Nat × Nat × ByteArray
  | 4 => String × List Glyph
  | 5 => List OutlineItem
  | 6 => List Link
  | 7 => ErrorKind × String
  | 8 => Unit
  | 9 => List Cell × List Nat × List Bool
  | 10 => List ViewLink
  | _ => Empty

/-- The payload codec of each response tag. -/
def responseCs : (t : Nat) → Codec (ResponseP t)
  | 0 => reject 0
  | 1 => pair nat (pair bool bool)
  | 2 => pair string (pair rat (pair rat nat))
  | 3 => pair nat (pair nat bytes)
  | 4 => pair string (list glyph glyph_ne)
  | 5 => list outlineItem outlineItem_ne
  | 6 => list link link_ne
  | 7 => pair errorKind string
  | 8 => unit
  | 9 => pair (list cell cell_ne) (pair (list nat nat_ne) (list bool bool_ne))
  | 10 => list viewLink viewLink_ne
  | t + 11 => reject (t + 11)

/-- `Response` as a tagged payload. -/
def Response.toSig : Response → (t : Nat) × ResponseP t
  | .docInfo n r e => ⟨1, (n, r, e)⟩
  | .pageInfo l w h r => ⟨2, (l, w, h, r)⟩
  | .image w h d => ⟨3, (w, h, d)⟩
  | .text s gs => ⟨4, (s, gs)⟩
  | .outline is => ⟨5, is⟩
  | .links ls => ⟨6, ls⟩
  | .error k m => ⟨7, (k, m)⟩
  | .bye => ⟨8, ()⟩
  | .pageIndex cs ds hs => ⟨9, (cs, ds, hs)⟩
  | .viewLinks ls => ⟨10, ls⟩

/-- The inverse of `Response.toSig`. -/
def Response.ofSig : (t : Nat) × ResponseP t → Response
  | ⟨0, e⟩ => e.elim
  | ⟨1, (n, r, e)⟩ => .docInfo n r e
  | ⟨2, (l, w, h, r)⟩ => .pageInfo l w h r
  | ⟨3, (w, h, d)⟩ => .image w h d
  | ⟨4, (s, gs)⟩ => .text s gs
  | ⟨5, is⟩ => .outline is
  | ⟨6, ls⟩ => .links ls
  | ⟨7, (k, m)⟩ => .error k m
  | ⟨8, _⟩ => .bye
  | ⟨9, (cs, ds, hs)⟩ => .pageIndex cs ds hs
  | ⟨10, ls⟩ => .viewLinks ls
  | ⟨_ + 11, e⟩ => e.elim

/-- **The response codec**: one tag byte, then the fields. -/
def response : Codec Response :=
  iso (sigma responseCs) Response.toSig Response.ofSig (fun x => by cases x <;> rfl)

/-! ## The protocol theorems, instantiated -/

/-- **Round trip (requests)**: a request whose numbers are in range (`request.valid`) decodes
from its encoding. -/
theorem request_roundtrip (m : Request) (hv : request.valid m = true) :
    decodeBody request (request.enc m) = .ok m :=
  decodeBody_rt request m hv

/-- **Round trip (responses)**. -/
theorem response_roundtrip (m : Response) (hv : response.valid m = true) :
    decodeBody response (response.enc m) = .ok m :=
  decodeBody_rt response m hv

/-- **Framed round trip (requests)**: a valid request within `requestCap` decodes from its
frame, and the next frame starts right after it. -/
theorem request_frame_roundtrip (l : Limits) (m : Request) (hv : request.valid m = true)
    (hs : (request.enc m).size ≤ requestCap l) :
    decodeFrame request (requestCap l) (encodeFrame request m) 0 =
      .ok m (encodeFrame request m).size :=
  decodeFrame_encodeFrame request hv hs (requestCap_lt l)

/-- **Framed round trip (responses)**. -/
theorem response_frame_roundtrip (l : Limits) (m : Response) (hv : response.valid m = true)
    (hs : (response.enc m).size ≤ responseCap l) :
    decodeFrame response (responseCap l) (encodeFrame response m) 0 =
      .ok m (encodeFrame response m).size :=
  decodeFrame_encodeFrame response hv hs (responseCap_lt l)

/-- **Framing (requests)**: a stream of encoded requests decodes back to the list. -/
theorem request_stream (l : Limits) (ms : List Request)
    (hv : ∀ m ∈ ms, request.valid m = true ∧ (request.enc m).size ≤ requestCap l) :
    decodeStream request (requestCap l) (encodeFrames request ms) = .ok ms :=
  decodeStream_encodeFrames request (requestCap_lt l) ms hv

/-- **Framing (responses)**. -/
theorem response_stream (l : Limits) (ms : List Response)
    (hv : ∀ m ∈ ms, response.valid m = true ∧ (response.enc m).size ≤ responseCap l) :
    decodeStream response (responseCap l) (encodeFrames response ms) = .ok ms :=
  decodeStream_encodeFrames response (responseCap_lt l) ms hv

/-- **No early message (requests)**: a strict prefix of a request frame is `incomplete`, never
a decoded message. -/
theorem request_prefix (l : Limits) (m : Request) (hs : (request.enc m).size ≤ requestCap l)
    {k : Nat} (hk : k < (encodeFrame request m).size) :
    decodeFrame request (requestCap l) ((encodeFrame request m).extract 0 k) 0 = .incomplete :=
  decodeFrame_prefix request hs (requestCap_lt l) hk

/-- **No early message (responses)**. -/
theorem response_prefix (l : Limits) (m : Response) (hs : (response.enc m).size ≤ responseCap l)
    {k : Nat} (hk : k < (encodeFrame response m).size) :
    decodeFrame response (responseCap l) ((encodeFrame response m).extract 0 k) 0 = .incomplete :=
  decodeFrame_prefix response hs (responseCap_lt l) hk

/-- **Bounded**: a decoded frame is never longer than the cap plus the header. -/
theorem frame_bounded {α : Type} (c : Codec α) {cap : Nat} {bs : ByteArray} {p q : Nat} {m : α}
    (h : decodeFrame c cap bs p = .ok m q) : q - p ≤ 4 + cap := by
  have := (decodeFrame_next_le c h).1; omega

/-! ## Helpers for the shells -/

/-- The frame of a response the worker sends: `r` itself when it is valid and within
`responseCap l`, else a `responseTooLarge` error (which always fits). -/
def frameResponse (l : Limits) (r : Response) : ByteArray :=
  let body := response.enc r
  if response.valid r && decide (body.size ≤ responseCap l) then header body.size ++ body
  else encodeFrame response (.error .responseTooLarge
    s!"response of {body.size} bytes exceeds the cap of {responseCap l} bytes")

/-- The frame of a request; `none` when it is not valid or above `requestCap l`. -/
def frameRequest (l : Limits) (r : Request) : Option ByteArray :=
  let body := request.enc r
  if request.valid r && decide (body.size ≤ requestCap l) then some (header body.size ++ body)
  else none

/-! ## Checks -/

/-- The error of a decode result, if any. -/
private def errOf {α : Type} : Except DecodeError α → Option DecodeError
  | .error e => some e
  | .ok _ => none

/-- `true` iff a stream decodes to exactly `ms`. -/
private def streamIs {α : Type} [DecidableEq α] (r : Except DecodeError (List α)) (ms : List α) : Bool :=
  match r with
  | .ok xs => xs == ms
  | .error _ => false

/-- Decode a whole frame buffer as one message. -/
private def roundTrip {α : Type} (c : Codec α) (cap : Nat) (m : α) : Option α :=
  match decodeFrame c cap (encodeFrame c m) 0 with
  | .ok m' _ => some m'
  | _ => none

private def sampleGlyph : Glyph :=
  { text := "fi", origin := ⟨-3/7, 1000000⟩, box := ⟨0, -1/5, 12, 8⟩, fontSize := 10, dir := 1,
    visible := false, item := 3, seq := 70000 }

private def sampleResponses : List Response :=
  [.docInfo 12 true false, .pageInfo "iv" (612) (792/7) 3, .image 2 1 ⟨#[1, 2, 3, 4, 5, 6, 7, 8]⟩,
   .text "Hello\nworld" [sampleGlyph, { sampleGlyph with text := "é", visible := true }],
   .outline [⟨"Intro", 0, .page 0 .fit, some (-3)⟩,
     ⟨"Sec", 1, .page 4 (.xyz (some ⟨-125, 1⟩) none (some ⟨15, 1⟩)), none⟩,
     ⟨"Odd", 2, .danglingDest (.unknown [70, 111, 111]), some 0⟩],
   .links [⟨⟨1, 2, 3, 4⟩, .uri "https://example.org"⟩, ⟨⟨0, 0, 0, 0⟩, .action "Launch"⟩,
     ⟨⟨5, 5, 6, 6⟩, .unresolved "chap1"⟩, ⟨⟨1, 1, 2, 2⟩, .none⟩],
   .error .malformed "bad", .bye,
   .pageIndex [⟨"H", "", ⟨100, 698, 107, 708⟩, 0⟩, ⟨"i", " ", ⟨1/3, -2, 5, 7/2⟩, 1⟩] [0, 1]
     [false, true],
   .viewLinks [⟨⟨1, 2, 3, 4⟩, .goto 3 (some (-1/2)) none⟩, ⟨⟨0, 0, 1, 1⟩, .uri "https://a.b/%20"⟩,
     ⟨⟨0, 0, 1, 1⟩, .badPage⟩, ⟨⟨0, 0, 1, 1⟩, .unresolved "x"⟩, ⟨⟨0, 0, 1, 1⟩, .other "Launch"⟩,
     ⟨⟨0, 0, 1, 1⟩, .none⟩]]

private def sampleRequests : List Request :=
  [.openDoc ⟨#[37, 80, 68, 70]⟩ false, .info, .pageInfo 0, .render 2 (3/2) 1 none,
   .render 0 1 0 (some { known := [(5, 0), (6, 0)], off := [(6, 0)] }), .text 0 true,
   .outline, .links 300, .quit, .pageIndex 4 none, .pageIndex 0 (some { known := [(1, 2)] }),
   .viewLinks 7]

#guard sampleRequests.all fun m => roundTrip request (requestCap {}) m == some m
#guard sampleResponses.all fun m => roundTrip response (responseCap {}) m == some m
-- A stream of frames decodes back to the list.
#guard streamIs (decodeStream request (requestCap {}) (encodeFrames request sampleRequests)) sampleRequests
#guard streamIs (decodeStream response (responseCap {}) (encodeFrames response sampleResponses)) sampleResponses
-- Every strict prefix of a frame is incomplete.
#guard let f := encodeFrame response (sampleResponses[3]?.getD .bye)
  (List.range f.size).all fun k => match decodeFrame response (responseCap {}) (f.extract 0 k) 0 with
    | .incomplete => true
    | _ => false
-- Malformed payloads are errors: tag 0, unknown tag 9, truncated field, trailing byte, bad UTF-8,
-- zero denominator, an over-long number, a list count above the bytes left.
#guard errOf (decodeBody request ⟨#[0]⟩) == some (.badTag 1 0)
#guard errOf (decodeBody request ⟨#[11]⟩) == some (.badTag 1 11)
#guard errOf (decodeBody request ⟨#[3]⟩) == some (.truncated 1)
#guard errOf (decodeBody request ⟨#[2, 0]⟩) == some (.trailing 1)
#guard errOf (decodeBody request ⟨#[1, 5, 1, 2]⟩) == some (.truncated 2)
#guard errOf (decodeBody response ⟨#[7, 1, 2, 0xC3, 0x28]⟩) == some (.badValue 2)
#guard errOf (decodeBody request ⟨#[4, 0, 2, 0]⟩) == some (.badValue 2)
#guard errOf (decodeBody request (⟨#[3]⟩ ++ ⟨(List.replicate 25 (0x80 : UInt8)).toArray⟩)) == some (.badValue 21)
#guard errOf (decodeBody response ⟨#[6, 100, 1]⟩) == some (.badValue 1)
#guard errOf (decodeBody request ⟨#[1, 0, 2]⟩) == some (.badValue 2)
-- An over-long frame header is an error, not a wait for more bytes.
#guard match decodeFrame request 10 (header 11 ++ ⟨#[2]⟩) 0 with
  | .error (.tooLong 11 10) => true
  | _ => false
-- Startup arguments: the default limits and a changed one round-trip through `--limits=`;
-- flags parse back; unknown flags and bad values are refused.
#guard (limitsOfHex? (limitsHex {})).map (·.maxPageSide) == some 16384
#guard (limitsOfHex? (limitsHex { maxPageSide := 77, maxOCDepth := 3 })).map
  (fun l => (l.maxPageSide, l.maxOCDepth, l.maxInputBytes)) == some (77, 3, 1 <<< 30)
#guard (limitsOfHex? "zz").isNone && (limitsOfHex? "0").isNone && (limitsOfHex? "").isNone
private def sampleStart : StartConfig :=
  { noSubst := true, home := some "/Users/a b", fontDirs := ["/x", "/y=z"], stallMs := 5,
    limits := { maxPageSide := 9 } }

#guard match StartConfig.ofArgs sampleStart.toArgs.toList with
  | .ok c => c.noSubst && c.home == some "/Users/a b" && c.fontDirs == ["/x", "/y=z"] &&
      c.stallMs == 5 && c.limits.maxPageSide == 9
  | .error _ => false
#guard match StartConfig.ofArgs [] with
  | .ok c => !c.noSubst && c.home.isNone && c.fontDirs.isEmpty && c.stallMs == 0
  | .error _ => false
#guard (match StartConfig.ofArgs ["--evil"] with | .error _ => true | .ok _ => false)
#guard (match StartConfig.ofArgs ["--limits=abc"] with | .error _ => true | .ok _ => false)
-- Out-of-range numbers are not valid (so the worker never sends them).
#guard !request.valid (.pageInfo (2 ^ 140)) && request.valid (.pageInfo (2 ^ 140 - 1))
#guard (frameRequest {} (.pageInfo (2 ^ 140))).isNone

end SafePdf.Shell.Worker.Protocol
