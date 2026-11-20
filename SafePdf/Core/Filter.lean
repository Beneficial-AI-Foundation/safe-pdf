import SafePdf.Core.Object
import SafePdf.Core.Filter.Flate
import SafePdf.Core.Filter.Predictor
import SafePdf.Core.Filter.Ascii
import SafePdf.Core.Filter.RunLength
import SafePdf.Core.Filter.LZW

set_option autoImplicit false

/-!
# The stream filter pipeline (Plan.md §6 Phase 3, §4 S3 and S7; task 3.5)

ISO 32000-2 §7.3.8.2: a stream dictionary's `/Filter` is a name or an array of names, applied
in order to decode the data; `/DecodeParms` is a dictionary (or `null`) for a single filter,
or an array of dictionaries / `null`s of the same length as the `/Filter` array. §7.4 lists
the standard filters. This module parses that chain (`parseChain`) and runs it
(`decodeStream`) with the verified decoders of `Core.Filter.*`.

## Rules

* F1. Names. The full names of §7.4 are accepted. The inline-image abbreviations of
  ISO 32000-2 Table 92 (`AHx A85 LZW Fl RL CCF DCT`) are accepted everywhere as well (as most
  readers do; the extra leniency is harmless since they name the same decoders). Any other
  name is `Error.unsupported`.
* F2. Shape. `/Filter` absent, `null`, a name, or an array of names (`[]` = no filter).
  At most `limits.maxFilters` (default 8) filters, else `Error.limitExceeded .filters`
  (task 3.9). An indirect `/Filter` or `/DecodeParms` (or array element) is
  `Error.unsupported`: the caller resolves references before calling (no resolver here).
* F3. Parameters. With no filter, `/DecodeParms` is ignored. Otherwise absent/`null` means
  "all defaults"; a dictionary is allowed only for exactly one filter; an array must have
  exactly as many elements as there are filters, each a dictionary or `null`. Anything else
  is `Error.malformed`.
* F4. Byte filters. `/FlateDecode` and `/LZWDecode` are followed by the predictor of their
  parameters (`Filter.Predictor`, ISO 32000-2 Table 10); `/LZWDecode` reads `/EarlyChange`.
  `/ASCIIHexDecode`, `/ASCII85Decode`, `/RunLengthDecode` take no parameters. `/Crypt` with
  `/Name /Identity` (the default) passes the data through; any other crypt filter is
  `Error.unsupported`. Decryption is not done here (task 4.3b): `Core.Open.OpenDoc.getObject`
  decrypts a stream's data before any filter runs, with the stream's own crypt filter when
  its first filter is `/Crypt` (`Core.Crypt.streamMethod`), and then marks that stage applied
  by setting its `/Name` to `/Identity` (`Core.Crypt.markApplied`, rule C7', task 4.6). So a
  named (non-Identity) crypt filter of an encrypted file **is accepted** here, as a
  pass-through, exactly when it was the one already applied; a named crypt filter that was
  not applied (an unencrypted file, a `/Metadata` stream left unencrypted, an indirect
  `/DecodeParms` that decryption did not read) is still `Error.unsupported`, never a silent
  pass-through of encrypted bytes. ISO 32000-2 §7.4.10: a `/Crypt` filter
  "shall be the first filter in the /Filter array"; a `/Crypt` stage in any other position
  is `Error.malformed` (task 3.9, `parseChain_crypt_first`).
* F5. Image codecs (S7). `/DCTDecode`, `/JPXDecode`, `/JBIG2Decode`, `/CCITTFaxDecode` are not
  decoded here: the chain stops and returns `Decoded.image codec parms bytes`, the output of
  the preceding filters, for the quarantine zone to decode later. An image codec must be the
  last filter; a filter after it is `Error.unsupported`.
* F6. Limits (S3). Every decoder bounds its output by `limits.maxDecodedStreamBytes`; the
  bytes returned (data or image payload) are checked against the same limit once more, which
  covers the stages that pass data through unchanged (no filter, `/Crypt /Identity`, an image
  codec right away). Hence `decodeStream_size_le`.
* F7. Strictness. `decodeStream` takes `strict` (default `true`), handed to every decoder
  (`strict := false` also skips Flate's Adler-32 check). The strict path is the default, as
  for the decoders themselves; the lenient flag exists for the repair path.
* F8. Structural streams. `decodeBytes` runs `decodeStream` for streams whose data the core
  itself reads (object streams, cross-reference streams; `Core.Xref.ObjStm`,
  `Core.Xref.Stream`): an image-codec result is an error chosen by the caller.
* F9. Reservation (task 8.10). The stream's `/DL` (`declaredLength`) is the expected decoded
  size; a `/FlateDecode` stage reserves its output buffer from it (`flateCap`, at most the
  stage's limit) instead of growing it by doubling. It never changes a result
  (`decodeOne_cap`, `applyStages_cap`, `applyStagesB_cap`, `decodeStream_eq`).

`decodeStream` decodes one stream. The aggregate bound it gives is `produced_le`: the bytes
allocated by all stages of one chain are at most `(number of stages) · maxDecodedStreamBytes`,
so at most `limits.maxFilters · maxDecodedStreamBytes` (`produced_le_maxFilters`).

## Document-wide accounting (task 3.10)

`decodeStreamB limits budget d raw : (Except Error Decoded) × Budget` is the budgeted entry
point: `Budget.remaining` is what is left of `limits.maxDecodedTotalBytes`
(`Budget.init limits`). The budget is returned **also on failure** (so the signature is a
pair, not `Except Error (Decoded × Budget)`): a failed attempt is charged too, since it may
have allocated bytes before failing; otherwise many streams that each inflate to just under
the per-stream limit and then fail (say, on the Adler-32) would cost unbounded work.

* B1. Each byte stage runs under the per-stream cap `min maxDecodedStreamBytes remaining`
  (`capped`) and is **charged its output**, intermediate stages included (they are
  allocated). `/Crypt /Identity` passes its input through and is charged it as well
  (conservative).
* B2. A failing byte stage is charged its cap (`failCharge`: the most it may have allocated);
  a failing `/Crypt` check allocates nothing and is free. Chain-parse errors (`parseChain`)
  are free: nothing is decoded.
* B3. A chain with no byte stage (no filter, or only an image codec) is charged its output,
  the raw bytes, so every returned byte is charged (`decodeStreamB_charge`).
* B4. Errors: a stage that hits a cap equal to the remaining budget (when that is below
  `maxDecodedStreamBytes`) reports `Error.limitExceeded .decodedTotalBytes` (`budgetErr`),
  as does an output larger than the remaining budget; the per-stream limit, when it is the
  binding one, still reports `.decodedStreamBytes`.
* B5. Charging is not refunded: the budget only decreases (`decodeStreamB_le`).

Which decodes of a document go through the budget is stated in `Core.Doc` (module doc,
"Decoded-bytes accounting").

## Theorems

* Totality by construction: the only recursion is structural on lists.
* `decodeStream_size_le`: the returned bytes are within `limits.maxDecodedStreamBytes`.
* `decodeStream_nil`: no `/Filter` ⇒ the data is returned unchanged (within the limit).
* `applyStages_image` / `decodeStream_image`: placeholder law — a chain `pre ++ [codec]`
  returns `.image codec parms b` where `.data b` is what `pre` decodes to.
* `decodeStream_unknown`: an unknown filter name gives `Error.unsupported`.
* `parseChain_length_le`, `produced_le`, `produced_le_maxFilters`: the aggregate bound.
* `decodeStream_too_many`: more than `limits.maxFilters` filters is
  `Error.limitExceeded .filters`.
* `parseChain_crypt_first`: a parsed chain has `/Crypt` at most as its first stage.
* `decodeBytes_size_le`: the structural-stream entry point keeps the per-stream bound.
* `decodeStreamB_le`: the budget never grows; `decodeStreamB_charge`: a successful result's
  bytes plus the budget left are at most the budget before (`decodeStreamB_exhausted`: with
  nothing left only empty outputs succeed); `decodeStreamB_size_le`: the per-stream bound.
* `decodeAllB_total`: over any sequence of budgeted decodes (`decodeAllB`), the bytes of all
  successful results plus the budget left are at most the initial budget;
  `decodeAllB_init`: from `Budget.init`, at most `limits.maxDecodedTotalBytes`.
-/

namespace SafePdf.Core.Filter

open SafePdf

/-! ## Filter descriptors -/

/-- Filters that turn bytes into bytes and are decoded in the verified core (§7.4.1–7.4.5,
§7.4.10). -/
inductive ByteFilter where
  /-- `/FlateDecode` (zlib, then predictor). -/
  | flate
  /-- `/LZWDecode` (then predictor). -/
  | lzw
  /-- `/ASCIIHexDecode`. -/
  | asciiHex
  /-- `/ASCII85Decode`. -/
  | ascii85
  /-- `/RunLengthDecode`. -/
  | runLength
  /-- `/Crypt` (only `/Identity` passes here; an applied named filter arrives as `/Identity`,
  rule F4). -/
  | crypt
  deriving Repr, DecidableEq, Inhabited

/-- Image codecs: never decoded in the trusted path (Plan.md §6 Phase 3, S7). -/
inductive ImageCodec where
  /-- `/DCTDecode` (JPEG). -/
  | dct
  /-- `/JPXDecode` (JPEG 2000). -/
  | jpx
  /-- `/JBIG2Decode`. -/
  | jbig2
  /-- `/CCITTFaxDecode`. -/
  | ccitt
  deriving Repr, DecidableEq, Inhabited

/-- The kind of one filter in a chain. -/
inductive Kind where
  /-- A byte filter decoded here. -/
  | byte (f : ByteFilter)
  /-- An image codec, handed on undecoded. -/
  | image (c : ImageCodec)
  deriving Repr, DecidableEq, Inhabited

/-- One stage of a filter chain: its kind and its `/DecodeParms` (`[]` for defaults). -/
structure Stage where
  /-- The filter. -/
  kind : Kind
  /-- Its parameters dictionary (`[]` when absent or `null`). -/
  parms : Dict

/-- The result of running a chain (F5). -/
inductive Decoded where
  /-- Fully decoded stream data. -/
  | data (bytes : ByteArray)
  /-- The chain reached an image codec: `bytes` is the output of the filters before it,
  still encoded with `codec` (parameters `parms`), to be decoded in the quarantine zone. -/
  | image (codec : ImageCodec) (parms : Dict) (bytes : ByteArray)

/-- The bytes carried by a result. -/
def Decoded.bytes : Decoded → ByteArray
  | .data b => b
  | .image _ _ b => b

/-- Filter names and abbreviations (F1). -/
def nameTable : List (String × Kind) :=
  [ ("FlateDecode", .byte .flate), ("Fl", .byte .flate),
    ("LZWDecode", .byte .lzw), ("LZW", .byte .lzw),
    ("ASCIIHexDecode", .byte .asciiHex), ("AHx", .byte .asciiHex),
    ("ASCII85Decode", .byte .ascii85), ("A85", .byte .ascii85),
    ("RunLengthDecode", .byte .runLength), ("RL", .byte .runLength),
    ("Crypt", .byte .crypt),
    ("DCTDecode", .image .dct), ("DCT", .image .dct),
    ("JPXDecode", .image .jpx),
    ("JBIG2Decode", .image .jbig2),
    ("CCITTFaxDecode", .image .ccitt), ("CCF", .image .ccitt) ]

/-- The filter a name denotes, if any (F1). -/
def kindOfName (n : Name) : Option Kind :=
  (nameTable.find? (fun p => Name.ofString p.1 == n)).map (·.2)

/-- A name as text, for error messages (bytes read as Latin-1). -/
def nameText (n : Name) : String :=
  String.ofList (n.bytes.map (fun b => Char.ofNat b.toNat))

/-! ## Parsing the chain (F2, F3) -/

/-- Names of a `/Filter` array; every element must be a name. -/
def namesOf : List PdfObject → Except Error (List Name)
  | [] => .ok []
  | o :: rest =>
    match o with
    | .name n =>
      match namesOf rest with
      | .error e => .error e
      | .ok ns => .ok (n :: ns)
    | .ref _ _ => .error (.unsupported "/Filter: indirect array element")
    | _ => .error (.malformed 0 "/Filter: array element is not a name")

/-- The `/Filter` names in order (F2), at most `limits.maxFilters` (else
`Error.limitExceeded .filters`). -/
def filterNames (limits : Limits) (d : Dict) : Except Error (List Name) :=
  match d.get? (Name.ofString "Filter") with
  | none => .ok []
  | some (.name n) => if 1 ≤ limits.maxFilters then .ok [n] else .error (.limitExceeded .filters)
  | some (.array items) =>
    if items.length ≤ limits.maxFilters then namesOf items
    else .error (.limitExceeded .filters)
  | some (.ref _ _) => .error (.unsupported "/Filter: indirect reference")
  | some _ => .error (.malformed 0 "/Filter is not a name or an array")

/-- Map names to filter kinds; the first unknown name is `unsupported` (F1). -/
def kindsOf : List Name → Except Error (List Kind)
  | [] => .ok []
  | n :: ns =>
    match kindOfName n with
    | none => .error (.unsupported s!"filter /{nameText n}")
    | some k =>
      match kindsOf ns with
      | .error e => .error e
      | .ok ks => .ok (k :: ks)

/-- Elements of a `/DecodeParms` array: dictionaries or `null` (F3). -/
def parmsOf : List PdfObject → Except Error (List Dict)
  | [] => .ok []
  | o :: rest =>
    match o with
    | .null =>
      match parmsOf rest with
      | .error e => .error e
      | .ok ps => .ok ([] :: ps)
    | .dict p =>
      match parmsOf rest with
      | .error e => .error e
      | .ok ps => .ok (p :: ps)
    | .ref _ _ => .error (.unsupported "/DecodeParms: indirect array element")
    | _ => .error (.malformed 0 "/DecodeParms: array element is not a dictionary or null")

/-- The parameter dictionaries for `n ≥ 1` filters (F3). -/
def parmsList (d : Dict) (n : Nat) : Except Error (List Dict) :=
  match d.get? (Name.ofString "DecodeParms") with
  | none => .ok (List.replicate n [])
  | some (.dict p) =>
    if n = 1 then .ok [p]
    else .error (.malformed 0 "/DecodeParms: a dictionary for a chain of several filters")
  | some (.array items) =>
    if items.length = n then parmsOf items
    else .error (.malformed 0 "/DecodeParms: array length differs from /Filter")
  | some (.ref _ _) => .error (.unsupported "/DecodeParms: indirect reference")
  | some _ => .error (.malformed 0 "/DecodeParms is not a dictionary or an array")

/-- Whether a stage is a `/Crypt` filter. -/
def Stage.isCrypt (s : Stage) : Bool := decide (s.kind = .byte .crypt)

/-- ISO 32000-2 §7.4.10: `/Crypt` only as the first stage (F4). -/
def cryptFirst (stages : List Stage) : Except Error (List Stage) :=
  if (stages.drop 1).any Stage.isCrypt then
    .error (.malformed 0 "/Crypt is not the first filter of the chain (ISO 32000-2 §7.4.10)")
  else .ok stages

/-- Parse the filter chain of a stream dictionary (F1–F4). -/
def parseChain (limits : Limits) (d : Dict) : Except Error (List Stage) :=
  match filterNames limits d with
  | .error e => .error e
  | .ok [] => .ok []
  | .ok names =>
    match kindsOf names with
    | .error e => .error e
    | .ok kinds =>
      match parmsList d kinds.length with
      | .error e => .error e
      | .ok ps => cryptFirst (List.zipWith Stage.mk kinds ps)

/-! ## One byte stage (F4) -/

/-- Undo the predictor of a `/DecodeParms` dictionary (identity when `/Predictor` is 1). -/
def predict (parms : Dict) (b : ByteArray) : Except Error ByteArray :=
  match Predictor.Params.ofDict parms with
  | .error e => .error e
  | .ok p => Predictor.decode p b

/-- `/Crypt` parameters: `/Name` absent or `/Identity` (F4). -/
def cryptCheck (parms : Dict) : Except Error Unit :=
  match parms.get? (Name.ofString "Name") with
  | none => .ok ()
  | some (.name n) =>
    if n = Name.ofString "Identity" then .ok ()
    else .error (.unsupported s!"/Crypt filter /{nameText n} (not applied by decryption)")
  | some _ => .error (.malformed 0 "/Crypt /DecodeParms /Name is not a name")

/-- The output capacity reserved for a `/FlateDecode` stage (task 8.10) from `cap`, the
expected size of the stream's decoded data (`declaredLength`): `cap` plus one filter-type byte
per row when a PNG predictor follows, at most the stage's limit and `2048` bytes per input
byte (beyond any DEFLATE ratio) plus `4096`. Only a reservation: the result does not depend on
it (`decodeOne_cap`), and it is never more than the stage may allocate anyway (B2). -/
def flateCap (limits : Limits) (parms : Dict) (cap n : Nat) : Nat :=
  let rows := match Predictor.Params.ofDict parms with
    | .ok p => if 10 ≤ p.predictor then cap / max 1 (Predictor.rowBytes p) + 1 else 0
    | .error _ => 0
  min (min (cap + rows) limits.maxDecodedStreamBytes) (2048 * n + 4096)

/-- Decode one byte stage (F4). `cap`: the expected decoded size, used only to reserve the
output buffer of `/FlateDecode` (`flateCap`, task 8.10; not observable, `decodeOne_cap`). -/
def decodeOne (limits : Limits) (strict : Bool) (f : ByteFilter) (parms : Dict)
    (b : ByteArray) (cap : Nat := 0) : Except Error ByteArray :=
  match f with
  | .flate =>
    match Flate.flateDecode limits b strict (flateCap limits parms cap b.size) with
    | .error e => .error e
    | .ok o => predict parms o
  | .lzw =>
    match LZW.earlyOfDict parms with
    | .error e => .error e
    | .ok early =>
      match LZW.lzwDecode limits b early strict with
      | .error e => .error e
      | .ok o => predict parms o
  | .asciiHex => Ascii.asciiHexDecode limits b strict
  | .ascii85 => Ascii.ascii85Decode limits b strict
  | .runLength => RunLength.runLengthDecode limits b strict
  | .crypt =>
    match cryptCheck parms with
    | .error e => .error e
    | .ok () => .ok b

/-- The reserved capacity does not change a stage's result. -/
theorem decodeOne_cap (limits : Limits) (strict : Bool) (f : ByteFilter) (parms : Dict)
    (b : ByteArray) (cap : Nat) :
    decodeOne limits strict f parms b cap = decodeOne limits strict f parms b := by
  cases f <;> simp only [decodeOne, Flate.flateDecode_cap]

/-- A predictor never grows its input. -/
theorem predict_size_le {parms : Dict} {b out : ByteArray} (h : predict parms b = .ok out) :
    out.size ≤ b.size := by
  unfold predict at h
  split at h
  · cases h
  · exact Predictor.decode_size_le _ _ _ h

/-- **Stage bound** for a decoding stage (anything but `/Crypt`): the output is within
`limits.maxDecodedStreamBytes`. -/
theorem decodeOne_size_le_of_ne {limits : Limits} {strict : Bool} {f : ByteFilter}
    {parms : Dict} {b out : ByteArray} (hf : f ≠ .crypt)
    (h : decodeOne limits strict f parms b = .ok out) :
    out.size ≤ limits.maxDecodedStreamBytes := by
  cases f with
  | flate =>
    simp only [decodeOne] at h
    split at h
    · cases h
    · rename_i o ho
      exact Nat.le_trans (predict_size_le h) (Flate.flateDecode_size_le ho)
  | lzw =>
    simp only [decodeOne] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i o ho
        exact Nat.le_trans (predict_size_le h) (LZW.lzwDecode_size_le ho)
  | asciiHex => exact Ascii.asciiHexDecode_size_le _ _ _ _ h
  | ascii85 => exact Ascii.ascii85Decode_size_le _ _ _ _ h
  | runLength => exact RunLength.runLengthDecode_size_le _ _ _ _ h
  | crypt => exact absurd rfl hf

/-- **Stage bound**: a byte stage either produces at most `limits.maxDecodedStreamBytes`
bytes or passes its input through unchanged (`/Crypt /Identity`). -/
theorem decodeOne_size_le {limits : Limits} {strict : Bool} {f : ByteFilter} {parms : Dict}
    {b out : ByteArray} (h : decodeOne limits strict f parms b = .ok out) :
    out.size ≤ limits.maxDecodedStreamBytes ∨ out = b := by
  by_cases hf : f = .crypt
  · subst hf
    simp only [decodeOne] at h
    split at h
    · cases h
    · simp only [Except.ok.injEq] at h; exact .inr h.symm
  · exact .inl (decodeOne_size_le_of_ne hf h)

/-! ## Running the chain (F5, F6) -/

/-- The per-stream output limit error. -/
def limitErr : Error := .limitExceeded .decodedStreamBytes

/-- Run the stages in order (F5, F6). Structural on the list. `cap`: the expected decoded
size, handed to every stage (`decodeOne`; a reservation only, `applyStages_cap`). -/
def applyStages (limits : Limits) (strict : Bool) (stages : List Stage) (b : ByteArray)
    (cap : Nat := 0) : Except Error Decoded :=
  match stages, b with
  | [], b =>
    if b.size ≤ limits.maxDecodedStreamBytes then .ok (.data b) else .error limitErr
  | ⟨.image c, p⟩ :: [], b =>
    if b.size ≤ limits.maxDecodedStreamBytes then .ok (.image c p b) else .error limitErr
  | ⟨.image _, _⟩ :: _ :: _, _ => .error (.unsupported "a filter after an image codec")
  | ⟨.byte f, p⟩ :: rest, b =>
    match decodeOne limits strict f p b cap with
    | .error e => .error e
    | .ok o => applyStages limits strict rest o cap

/-- The reserved capacity does not change the result of a chain. -/
theorem applyStages_cap (limits : Limits) (strict : Bool) :
    (stages : List Stage) → (b : ByteArray) → (cap : Nat) →
    applyStages limits strict stages b cap = applyStages limits strict stages b
  | [], _, _ => rfl
  | ⟨.image _, _⟩ :: [], _, _ => rfl
  | ⟨.image _, _⟩ :: _ :: _, _, _ => rfl
  | ⟨.byte f, p⟩ :: rest, b, cap => by
    simp only [applyStages, decodeOne_cap]
    split
    · rfl
    · exact applyStages_cap limits strict rest _ cap

/-- The `/DL` entry of a stream dictionary (ISO 32000-2 §7.3.8.2, Table 5: the number of bytes
of the decoded stream, "a hint"), `0` when absent or not a non-negative integer. Used only to
reserve output buffers (task 8.10); a wrong value costs at most a reallocation or an unused
reservation within the stage's limit. -/
def declaredLength (d : Dict) : Nat :=
  match d.get? (Name.ofString "DL") with
  | some (.int i) => i.toNat
  | _ => 0

/-- **Entry point.** Decode a stream's data `raw` with the filter chain of its dictionary
`d` (ISO 32000-2 §7.3.8, §7.4). Strict by default (F7). `/DL` (`declaredLength`) sizes the
output buffers (task 8.10) and does not change the result (`decodeStream_eq`). -/
def decodeStream (limits : Limits) (d : Dict) (raw : ByteArray) (strict : Bool := true) :
    Except Error Decoded :=
  match parseChain limits d with
  | .error e => .error e
  | .ok stages => applyStages limits strict stages raw (declaredLength d)

/-- `decodeStream` is the chain run without a reservation. -/
theorem decodeStream_eq (limits : Limits) (d : Dict) (raw : ByteArray) (strict : Bool) :
    decodeStream limits d raw strict =
      match parseChain limits d with
      | .error e => .error e
      | .ok stages => applyStages limits strict stages raw := by
  unfold decodeStream
  split <;> simp only [applyStages_cap]

/-- **Structural streams (F8).** Decode a stream whose data the core reads itself (an object
stream or a cross-reference stream) with `decodeStream`; an image-codec result, meaningless
for such a stream, is the error `imageErr`. -/
def decodeBytes (limits : Limits) (d : Dict) (raw : ByteArray) (imageErr : Error)
    (strict : Bool := true) : Except Error ByteArray :=
  match decodeStream limits d raw strict with
  | .error e => .error e
  | .ok (.data b) => .ok b
  | .ok (.image _ _ _) => .error imageErr

/-! ## Theorems -/

/-- The bytes returned by `applyStages` are within the per-stream limit. -/
theorem applyStages_size_le (limits : Limits) (strict : Bool) :
    (stages : List Stage) → (b : ByteArray) → (r : Decoded) →
    applyStages limits strict stages b = .ok r → r.bytes.size ≤ limits.maxDecodedStreamBytes
  | [], b, r, h => by
    simp only [applyStages] at h
    split at h
    · simp only [Except.ok.injEq] at h; subst h; assumption
    · cases h
  | ⟨.image c, p⟩ :: [], b, r, h => by
    simp only [applyStages] at h
    split at h
    · simp only [Except.ok.injEq] at h; subst h; assumption
    · cases h
  | ⟨.image _, _⟩ :: _ :: _, _, _, h => by simp [applyStages] at h
  | ⟨.byte f, p⟩ :: rest, b, r, h => by
    simp only [applyStages] at h
    split at h
    · cases h
    · exact applyStages_size_le limits strict rest _ r h

/-- **Output bound (S3)**: a successful `decodeStream` returns at most
`limits.maxDecodedStreamBytes` bytes, whether fully decoded or an image payload. -/
theorem decodeStream_size_le {limits : Limits} {d : Dict} {raw : ByteArray} {strict : Bool}
    {r : Decoded} (h : decodeStream limits d raw strict = .ok r) :
    r.bytes.size ≤ limits.maxDecodedStreamBytes := by
  rw [decodeStream_eq] at h
  split at h
  · cases h
  · exact applyStages_size_le limits strict _ raw r h

/-- **Output bound** for structural streams: `decodeBytes` returns at most
`limits.maxDecodedStreamBytes` bytes. -/
theorem decodeBytes_size_le {limits : Limits} {d : Dict} {raw : ByteArray} {imageErr : Error}
    {strict : Bool} {out : ByteArray} (h : decodeBytes limits d raw imageErr strict = .ok out) :
    out.size ≤ limits.maxDecodedStreamBytes := by
  unfold decodeBytes at h
  split at h
  · cases h
  · rename_i b hb
    simp only [Except.ok.injEq] at h; subst h
    exact decodeStream_size_le hb
  · cases h

/-- With no `/Filter` there are no stages. -/
theorem parseChain_nil {limits : Limits} {d : Dict} (h : d.get? (Name.ofString "Filter") = none) :
    parseChain limits d = .ok [] := by
  simp [parseChain, filterNames, h]

/-- **No filter**: without `/Filter` the data is returned unchanged (when within the
per-stream limit; otherwise `Error.limitExceeded .decodedStreamBytes`). `/DecodeParms` is
ignored. -/
theorem decodeStream_nil {limits : Limits} {d : Dict} {raw : ByteArray} {strict : Bool}
    (h : d.get? (Name.ofString "Filter") = none)
    (hs : raw.size ≤ limits.maxDecodedStreamBytes) :
    decodeStream limits d raw strict = .ok (.data raw) := by
  simp [decodeStream, parseChain_nil h, applyStages, hs]

/-- **Placeholder law (S7)**: if the prefix `pre` decodes to data `b`, the chain
`pre ++ [codec]` returns `b` tagged with the image codec and its parameters. -/
theorem applyStages_image (limits : Limits) (strict : Bool) (c : ImageCodec) (p : Dict) :
    (pre : List Stage) → (raw b : ByteArray) →
    applyStages limits strict pre raw = .ok (.data b) →
    applyStages limits strict (pre ++ [⟨.image c, p⟩]) raw = .ok (.image c p b)
  | [], raw, b, h => by
    simp only [applyStages] at h
    split at h
    · rename_i hs
      simp only [Except.ok.injEq, Decoded.data.injEq] at h
      subst h
      simp [applyStages, hs]
    · cases h
  | ⟨.image _, _⟩ :: [], _, _, h => by
    simp only [applyStages] at h
    split at h <;> simp at h
  | ⟨.image _, _⟩ :: _ :: _, _, _, h => by simp [applyStages] at h
  | ⟨.byte f, q⟩ :: rest, raw, b, h => by
    simp only [applyStages] at h
    simp only [List.cons_append, applyStages]
    split at h
    · cases h
    · rename_i o _
      exact applyStages_image limits strict c p rest o b h

/-- **Placeholder law** for `decodeStream`: when the chain parses as `pre ++ [codec]` and
`pre` decodes to `b`, the result is `.image codec parms b`. -/
theorem decodeStream_image {limits : Limits} {d : Dict} {raw b : ByteArray} {strict : Bool}
    {pre : List Stage} {c : ImageCodec} {p : Dict}
    (hc : parseChain limits d = .ok (pre ++ [⟨.image c, p⟩]))
    (hp : applyStages limits strict pre raw = .ok (.data b)) :
    decodeStream limits d raw strict = .ok (.image c p b) := by
  rw [decodeStream_eq]
  simp only [hc]
  exact applyStages_image limits strict c p pre raw b hp

/-- An unknown name anywhere in the list makes `kindsOf` fail with `unsupported`. -/
theorem kindsOf_unknown : (ns : List Name) → (∃ n ∈ ns, kindOfName n = none) →
    ∃ msg, kindsOf ns = .error (.unsupported msg)
  | [], ⟨_, hn, _⟩ => by simp at hn
  | n :: ns, ⟨m, hm, hk⟩ => by
    simp only [kindsOf]
    cases hn : kindOfName n with
    | none => exact ⟨_, rfl⟩
    | some k =>
      simp only
      have hm' : m ∈ ns := by
        rcases List.mem_cons.mp hm with h | h
        · subst h; rw [hn] at hk; cases hk
        · exact h
      obtain ⟨msg, hmsg⟩ := kindsOf_unknown ns ⟨m, hm', hk⟩
      exact ⟨msg, by rw [hmsg]⟩

/-- **Unknown filter**: if the `/Filter` names include one that is not a known filter, the
stream is `Error.unsupported` (whatever `/DecodeParms` holds). -/
theorem decodeStream_unknown {limits : Limits} {d : Dict} {raw : ByteArray} {strict : Bool}
    {ns : List Name} (hf : filterNames limits d = .ok ns) (hu : ∃ n ∈ ns, kindOfName n = none) :
    ∃ msg, decodeStream limits d raw strict = .error (.unsupported msg) := by
  obtain ⟨msg, hmsg⟩ := kindsOf_unknown ns hu
  refine ⟨msg, ?_⟩
  cases ns with
  | nil => obtain ⟨_, hn, _⟩ := hu; simp at hn
  | cons n rest =>
    simp only [decodeStream, parseChain, hf, hmsg]

/-- Special case: a single unknown `/Filter` name is `unsupported`. -/
theorem decodeStream_unknown_name {limits : Limits} {d : Dict} {raw : ByteArray}
    {strict : Bool} {n : Name} (hf : d.get? (Name.ofString "Filter") = some (.name n))
    (hm : 1 ≤ limits.maxFilters) (hk : kindOfName n = none) :
    ∃ msg, decodeStream limits d raw strict = .error (.unsupported msg) :=
  decodeStream_unknown (ns := [n]) (by simp [filterNames, hf, hm]) ⟨n, by simp, hk⟩

/-! ## Aggregate bound across stages -/

/-- `namesOf` keeps the length. -/
theorem namesOf_length : (items : List PdfObject) → (ns : List Name) →
    namesOf items = .ok ns → ns.length = items.length
  | [], ns, h => by simp only [namesOf, Except.ok.injEq] at h; subst h; rfl
  | o :: rest, ns, h => by
    simp only [namesOf] at h
    split at h
    · split at h
      · cases h
      · rename_i ns' h'
        simp only [Except.ok.injEq] at h; subst h
        simp [namesOf_length rest ns' h']
    · cases h
    · cases h

/-- At most `limits.maxFilters` names. -/
theorem filterNames_length_le {limits : Limits} {d : Dict} {ns : List Name}
    (h : filterNames limits d = .ok ns) : ns.length ≤ limits.maxFilters := by
  unfold filterNames at h
  split at h
  · simp only [Except.ok.injEq] at h; subst h; simp
  · split at h
    · rename_i hm; simp only [Except.ok.injEq] at h; subst h; simpa using hm
    · cases h
  · split at h
    · rename_i hl; rw [namesOf_length _ _ h]; exact hl
    · cases h
  · cases h
  · cases h

/-- `kindsOf` keeps the length. -/
theorem kindsOf_length : (ns : List Name) → (ks : List Kind) →
    kindsOf ns = .ok ks → ks.length = ns.length
  | [], ks, h => by simp only [kindsOf, Except.ok.injEq] at h; subst h; rfl
  | n :: rest, ks, h => by
    simp only [kindsOf] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i ks' h'
        simp only [Except.ok.injEq] at h; subst h
        simp [kindsOf_length rest ks' h']

/-- `cryptFirst` returns its argument or fails. -/
theorem cryptFirst_eq {stages out : List Stage} (h : cryptFirst stages = .ok out) :
    out = stages := by
  unfold cryptFirst at h
  split at h
  · cases h
  · simp only [Except.ok.injEq] at h; exact h.symm

/-- **Chain length**: a parsed chain has at most `limits.maxFilters` stages. -/
theorem parseChain_length_le {limits : Limits} {d : Dict} {stages : List Stage}
    (h : parseChain limits d = .ok stages) : stages.length ≤ limits.maxFilters := by
  cases hn : filterNames limits d with
  | error e => simp [parseChain, hn] at h
  | ok names =>
    have hl := filterNames_length_le hn
    cases names with
    | nil =>
      simp only [parseChain, hn, Except.ok.injEq] at h; subst h; simp
    | cons n ns =>
      simp only [parseChain, hn] at h
      cases hk : kindsOf (n :: ns) with
      | error e => simp [hk] at h
      | ok kinds =>
        cases hp : parmsList d kinds.length with
        | error e => simp [hk, hp] at h
        | ok ps =>
          simp only [hk, hp] at h
          rw [cryptFirst_eq h, List.length_zipWith, kindsOf_length _ _ hk]
          exact Nat.le_trans (Nat.min_le_left _ _) hl

/-- **Crypt first (ISO 32000-2 §7.4.10)**: in a parsed chain, no stage after the first is a
`/Crypt` filter. -/
theorem parseChain_crypt_first {limits : Limits} {d : Dict} {stages : List Stage}
    (h : parseChain limits d = .ok stages) : ∀ s ∈ stages.drop 1, s.kind ≠ .byte .crypt := by
  have hc : ∀ xs out : List Stage, cryptFirst xs = .ok out →
      ∀ s ∈ out.drop 1, s.kind ≠ .byte .crypt := by
    intro xs out hx s hs hk
    unfold cryptFirst at hx
    split at hx
    · cases hx
    · rename_i hn
      simp only [Except.ok.injEq] at hx; subst hx
      exact hn (List.any_eq_true.mpr ⟨s, hs, by simp [Stage.isCrypt, hk]⟩)
  unfold parseChain at h
  split at h
  · cases h
  · simp only [Except.ok.injEq] at h; subst h; simp
  · split at h
    · cases h
    · split at h
      · cases h
      · exact hc _ _ h

/-- **Filter-count limit**: a `/Filter` array of more than `limits.maxFilters` names is
`Error.limitExceeded .filters`, before any byte is decoded. -/
theorem decodeStream_too_many {limits : Limits} {d : Dict} {raw : ByteArray} {strict : Bool}
    {items : List PdfObject} (hf : d.get? (Name.ofString "Filter") = some (.array items))
    (hl : limits.maxFilters < items.length) :
    decodeStream limits d raw strict = .error (.limitExceeded .filters) := by
  have hn : filterNames limits d = .error (.limitExceeded .filters) := by
    simp only [filterNames, hf]
    simp only [show ¬ items.length ≤ limits.maxFilters by omega, ↓reduceIte]
  simp [decodeStream, parseChain, hn]

/-- Bytes allocated by the stages of a chain run on `b`: each decoding stage counts its
output size, a failing stage counts the full limit (it may have allocated that much before
failing), a pass-through (`/Crypt /Identity`) and an image codec allocate nothing. This
mirrors `applyStages` stage by stage. -/
def produced (limits : Limits) (strict : Bool) : List Stage → ByteArray → Nat
  | [], _ => 0
  | ⟨.image _, _⟩ :: _, _ => 0
  | ⟨.byte f, p⟩ :: rest, b =>
    match decodeOne limits strict f p b with
    | .error _ => limits.maxDecodedStreamBytes
    | .ok o =>
      (if f = .crypt then 0 else o.size) + produced limits strict rest o

/-- **Aggregate bound**: a chain of `n` stages allocates at most `n · maxDecodedStreamBytes`
bytes in total. -/
theorem produced_le (limits : Limits) (strict : Bool) :
    (stages : List Stage) → (b : ByteArray) →
    produced limits strict stages b ≤ stages.length * limits.maxDecodedStreamBytes
  | [], _ => by simp [produced]
  | ⟨.image _, _⟩ :: _, _ => by simp [produced]
  | ⟨.byte f, p⟩ :: rest, b => by
    simp only [produced, List.length_cons, Nat.succ_mul]
    split
    · omega
    · rename_i o ho
      have ih := produced_le limits strict rest o
      have hst : (if f = .crypt then 0 else o.size) ≤ limits.maxDecodedStreamBytes := by
        by_cases hf : f = .crypt
        · simp [hf]
        · simp only [hf, ↓reduceIte]
          exact decodeOne_size_le_of_ne hf ho
      omega

/-- **Aggregate bound for a stream**: decoding the chain of `d` allocates at most
`limits.maxFilters · maxDecodedStreamBytes` bytes. -/
theorem produced_le_maxFilters {limits : Limits} {strict : Bool} {d : Dict}
    {stages : List Stage} (h : parseChain limits d = .ok stages) (b : ByteArray) :
    produced limits strict stages b ≤ limits.maxFilters * limits.maxDecodedStreamBytes :=
  Nat.le_trans (produced_le limits strict stages b)
    (Nat.mul_le_mul_right _ (parseChain_length_le h))

/-! ## Document-wide accounting (task 3.10, S3)

The budgeted entry point `decodeStreamB` threads a `Budget` (bytes still allowed under
`limits.maxDecodedTotalBytes`) through one decode and returns it, charged, **also on
failure**: a failed attempt may have allocated bytes too (rules B1–B5 in the module doc). -/

/-- What is left of the document-wide decoded-bytes budget (S3). Start from `Budget.init`. -/
structure Budget where
  /-- Bytes that may still be decoded. -/
  remaining : Nat
  deriving Repr, DecidableEq, Inhabited

/-- The full budget of a document: `limits.maxDecodedTotalBytes`. -/
def Budget.init (limits : Limits) : Budget := ⟨limits.maxDecodedTotalBytes⟩

/-- The total-budget error. -/
def totalErr : Error := .limitExceeded .decodedTotalBytes

/-- The limits for one budgeted stage: the per-stream cap lowered to the remaining budget. -/
def capped (limits : Limits) (rem : Nat) : Limits :=
  { limits with maxDecodedStreamBytes := min limits.maxDecodedStreamBytes rem }

/-- Report a per-stream limit hit as a total-budget hit when the budget was the binding cap
(B4). -/
def budgetErr (limits : Limits) (rem : Nat) (e : Error) : Error :=
  match e with
  | .limitExceeded .decodedStreamBytes =>
    if rem < limits.maxDecodedStreamBytes then totalErr else e
  | _ => e

/-- The charge of a failed byte stage (B2): its cap (it may have allocated that much before
failing), except `/Crypt`, which allocates nothing. -/
def failCharge (limits : Limits) (rem : Nat) (f : ByteFilter) : Nat :=
  if f = .crypt then 0 else min limits.maxDecodedStreamBytes rem

/-- Whether a stage is a byte filter. -/
def Stage.isByte (s : Stage) : Bool :=
  match s.kind with
  | .byte _ => true
  | .image _ => false

/-- Whether a chain has a byte stage. -/
def hasByte (stages : List Stage) : Bool := stages.any Stage.isByte

/-- `applyStages` with the budget `rem` threaded through (B1, B2): each byte stage runs
under `capped limits rem` and is charged its output; a failing byte stage is charged
`failCharge`. Returns the result and the remaining budget. Structural on the list. -/
def applyStagesB (limits : Limits) (strict : Bool) (stages : List Stage) (rem : Nat)
    (b : ByteArray) (cap : Nat := 0) : Except Error Decoded × Nat :=
  match stages, rem, b with
  | [], rem, b =>
    (if b.size ≤ limits.maxDecodedStreamBytes then .ok (.data b) else .error limitErr, rem)
  | ⟨.image c, p⟩ :: [], rem, b =>
    (if b.size ≤ limits.maxDecodedStreamBytes then .ok (.image c p b) else .error limitErr,
      rem)
  | ⟨.image _, _⟩ :: _ :: _, rem, _ => (.error (.unsupported "a filter after an image codec"), rem)
  | ⟨.byte f, p⟩ :: rest, rem, b =>
    match decodeOne (capped limits rem) strict f p b cap with
    | .error e => (.error (budgetErr limits rem e), rem - failCharge limits rem f)
    | .ok o =>
      if o.size ≤ rem then applyStagesB limits strict rest (rem - o.size) o cap
      else (.error totalErr, rem)

/-- The reserved capacity does not change the budgeted result of a chain. -/
theorem applyStagesB_cap (limits : Limits) (strict : Bool) :
    (stages : List Stage) → (rem : Nat) → (b : ByteArray) → (cap : Nat) →
    applyStagesB limits strict stages rem b cap = applyStagesB limits strict stages rem b
  | [], _, _, _ => rfl
  | ⟨.image _, _⟩ :: [], _, _, _ => rfl
  | ⟨.image _, _⟩ :: _ :: _, _, _, _ => rfl
  | ⟨.byte f, p⟩ :: rest, rem, b, cap => by
    simp only [applyStagesB, decodeOne_cap]
    split
    · rfl
    · split
      · exact applyStagesB_cap limits strict rest _ _ cap
      · rfl

/-- **Budgeted entry point** (task 3.10). Decode like `decodeStream`, charging the bytes
produced against `budget` (rules B1–B5). Returns the result and the charged budget, also on
failure. -/
def decodeStreamB (limits : Limits) (budget : Budget) (d : Dict) (raw : ByteArray)
    (strict : Bool := true) : (Except Error Decoded) × Budget :=
  match parseChain limits d with
  | .error e => (.error e, budget)
  | .ok stages =>
    if hasByte stages then
      let p := applyStagesB limits strict stages budget.remaining raw (declaredLength d)
      (p.1, ⟨p.2⟩)
    else
      match applyStages limits strict stages raw with
      | .error e => (.error e, budget)
      | .ok r =>
        if r.bytes.size ≤ budget.remaining then (.ok r, ⟨budget.remaining - r.bytes.size⟩)
        else (.error totalErr, budget)

/-- Budgeted decoding of a sequence of streams (dictionary, raw data), threading the budget
from one to the next. -/
def decodeAllB (limits : Limits) (strict : Bool) :
    Budget → List (Dict × ByteArray) → List (Except Error Decoded) × Budget
  | b, [] => ([], b)
  | b, (d, raw) :: xs =>
    let p := decodeStreamB limits b d raw strict
    let q := decodeAllB limits strict p.2 xs
    (p.1 :: q.1, q.2)

/-- Size of a successful result's bytes, `0` for an error. -/
def okSize : Except Error Decoded → Nat
  | .ok r => r.bytes.size
  | .error _ => 0

/-- The budget never grows in `applyStagesB`. -/
theorem applyStagesB_le (limits : Limits) (strict : Bool) :
    (stages : List Stage) → (rem : Nat) → (b : ByteArray) →
    (applyStagesB limits strict stages rem b).2 ≤ rem
  | [], rem, b => by simp [applyStagesB]
  | ⟨.image _, _⟩ :: [], rem, b => by simp [applyStagesB]
  | ⟨.image _, _⟩ :: _ :: _, rem, _ => by simp [applyStagesB]
  | ⟨.byte f, p⟩ :: rest, rem, b => by
    cases ho : decodeOne (capped limits rem) strict f p b with
    | error e => simp only [applyStagesB, ho]; exact Nat.sub_le _ _
    | ok o =>
      simp only [applyStagesB, ho]
      by_cases hs : o.size ≤ rem
      · simp only [hs, ↓reduceIte]
        have := applyStagesB_le limits strict rest (rem - o.size) o
        omega
      · simp only [hs, ↓reduceIte]; exact Nat.le_refl _

/-- Without a byte stage, a successful `applyStagesB` returns its input bytes. -/
theorem applyStagesB_nobyte (limits : Limits) (strict : Bool) :
    (stages : List Stage) → (rem : Nat) → (b : ByteArray) → (r : Decoded) →
    hasByte stages = false → (applyStagesB limits strict stages rem b).1 = .ok r →
    r.bytes = b
  | [], rem, b, r, _, h => by
    simp only [applyStagesB] at h
    split at h
    · simp only [Except.ok.injEq] at h; subst h; rfl
    · cases h
  | ⟨.image _, _⟩ :: [], rem, b, r, _, h => by
    simp only [applyStagesB] at h
    split at h
    · simp only [Except.ok.injEq] at h; subst h; rfl
    · cases h
  | ⟨.image _, _⟩ :: _ :: _, rem, _, r, _, h => by simp [applyStagesB] at h
  | ⟨.byte _, _⟩ :: _, _, _, _, hb, _ => by simp [hasByte, Stage.isByte] at hb

/-- **Charge law** of `applyStagesB`: a success is within the per-stream limit, and when a
byte stage ran, its bytes were charged. -/
theorem applyStagesB_ok (limits : Limits) (strict : Bool) :
    (stages : List Stage) → (rem : Nat) → (b : ByteArray) → (r : Decoded) →
    (applyStagesB limits strict stages rem b).1 = .ok r →
    r.bytes.size ≤ limits.maxDecodedStreamBytes ∧
    (hasByte stages = true → r.bytes.size + (applyStagesB limits strict stages rem b).2 ≤ rem)
  | [], rem, b, r, h => by
    refine ⟨?_, fun hb => by simp [hasByte] at hb⟩
    simp only [applyStagesB] at h
    split at h
    · simp only [Except.ok.injEq] at h; subst h; assumption
    · cases h
  | ⟨.image _, _⟩ :: [], rem, b, r, h => by
    refine ⟨?_, fun hb => by simp [hasByte, Stage.isByte] at hb⟩
    simp only [applyStagesB] at h
    split at h
    · simp only [Except.ok.injEq] at h; subst h; assumption
    · cases h
  | ⟨.image _, _⟩ :: _ :: _, rem, _, r, h => by simp [applyStagesB] at h
  | ⟨.byte f, p⟩ :: rest, rem, b, r, h => by
    cases ho : decodeOne (capped limits rem) strict f p b with
    | error e => simp [applyStagesB, ho] at h
    | ok o =>
      by_cases hs : o.size ≤ rem
      · simp only [applyStagesB, ho, hs, ↓reduceIte] at h ⊢
        have ih := applyStagesB_ok limits strict rest (rem - o.size) o r h
        refine ⟨ih.1, fun _ => ?_⟩
        cases hr : hasByte rest
        · have heq := applyStagesB_nobyte limits strict rest (rem - o.size) o r hr h
          have hle := applyStagesB_le limits strict rest (rem - o.size) o
          rw [heq]; omega
        · have := ih.2 hr; omega
      · simp [applyStagesB, ho, hs] at h

/-- **Budget monotone**: `decodeStreamB` never increases the budget. -/
theorem decodeStreamB_le (limits : Limits) (budget : Budget) (d : Dict) (raw : ByteArray)
    (strict : Bool) : (decodeStreamB limits budget d raw strict).2.remaining ≤ budget.remaining := by
  unfold decodeStreamB
  split
  · exact Nat.le_refl _
  · split
    · simp only [applyStagesB_cap]; exact applyStagesB_le limits strict _ _ raw
    · split
      · exact Nat.le_refl _
      · split
        · exact Nat.sub_le _ _
        · exact Nat.le_refl _

/-- **Charge law** (S3): a successful `decodeStreamB` returns bytes that were charged: their
size plus the remaining budget is at most the budget before the call. -/
theorem decodeStreamB_charge {limits : Limits} {budget : Budget} {d : Dict} {raw : ByteArray}
    {strict : Bool} {r : Decoded} (h : (decodeStreamB limits budget d raw strict).1 = .ok r) :
    r.bytes.size + (decodeStreamB limits budget d raw strict).2.remaining ≤ budget.remaining := by
  cases hp : parseChain limits d with
  | error e => simp [decodeStreamB, hp] at h
  | ok stages =>
    cases hb : hasByte stages with
    | true =>
      simp only [decodeStreamB, hp, hb, ↓reduceIte, applyStagesB_cap] at h ⊢
      exact (applyStagesB_ok limits strict stages budget.remaining raw r h).2 hb
    | false =>
      cases hr : applyStages limits strict stages raw with
      | error e => simp [decodeStreamB, hp, hb, hr] at h
      | ok r' =>
        by_cases hs : r'.bytes.size ≤ budget.remaining
        · simp only [decodeStreamB, hp, hb, hr, hs, Bool.false_eq_true, ↓reduceIte,
            Except.ok.injEq] at h ⊢
          subst h; omega
        · simp [decodeStreamB, hp, hb, hr, hs] at h

/-- **Per-stream bound** for the budgeted entry point. -/
theorem decodeStreamB_size_le {limits : Limits} {budget : Budget} {d : Dict} {raw : ByteArray}
    {strict : Bool} {r : Decoded} (h : (decodeStreamB limits budget d raw strict).1 = .ok r) :
    r.bytes.size ≤ limits.maxDecodedStreamBytes := by
  unfold decodeStreamB at h
  split at h
  · cases h
  · split at h
    · simp only [applyStagesB_cap] at h; exact (applyStagesB_ok limits strict _ _ raw r h).1
    · split at h
      · cases h
      · rename_i r' hr
        split at h
        · simp only [Except.ok.injEq] at h; subst h
          exact applyStages_size_le limits strict _ raw _ hr
        · cases h

/-- **Exhausted budget**: with nothing left, only empty outputs succeed. -/
theorem decodeStreamB_exhausted {limits : Limits} {budget : Budget} {d : Dict}
    {raw : ByteArray} {strict : Bool} {r : Decoded} (h0 : budget.remaining = 0)
    (h : (decodeStreamB limits budget d raw strict).1 = .ok r) : r.bytes.size = 0 := by
  have := decodeStreamB_charge h
  omega

/-- **Document-wide bound** (S3): over any sequence of budgeted decodes, the bytes of all
successful results plus the budget left are at most the initial budget. -/
theorem decodeAllB_total (limits : Limits) (strict : Bool) :
    (b : Budget) → (xs : List (Dict × ByteArray)) →
    ((decodeAllB limits strict b xs).1.map okSize).sum +
      (decodeAllB limits strict b xs).2.remaining ≤ b.remaining
  | b, [] => by simp [decodeAllB]
  | b, (d, raw) :: xs => by
    have ih := decodeAllB_total limits strict (decodeStreamB limits b d raw strict).2 xs
    simp only [decodeAllB, List.map_cons, List.sum_cons]
    cases hr : (decodeStreamB limits b d raw strict).1 with
    | error e =>
      have := decodeStreamB_le limits b d raw strict
      simp only [okSize]; omega
    | ok r =>
      have := decodeStreamB_charge hr
      simp only [okSize]; omega

/-- **Document-wide bound from the start**: decoding any sequence of streams from
`Budget.init limits` yields at most `limits.maxDecodedTotalBytes` bytes of results. -/
theorem decodeAllB_init (limits : Limits) (strict : Bool) (xs : List (Dict × ByteArray)) :
    ((decodeAllB limits strict (Budget.init limits) xs).1.map okSize).sum ≤
      limits.maxDecodedTotalBytes :=
  Nat.le_trans (Nat.le_add_right _ _) (decodeAllB_total limits strict (Budget.init limits) xs)

/-! ## Tests -/

section Tests

/-- A name object (test helper). -/
private def N (s : String) : PdfObject := .name (Name.ofString s)

/-- A one-entry dictionary key (test helper). -/
private def K (s : String) : Name := Name.ofString s

/-- Bytes from a list. -/
private def B (l : List UInt8) : ByteArray := ⟨l.toArray⟩

/-- Default limits. -/
private def dl : Limits := {}

/-- Limits with a tiny per-stream output cap. -/
private def tiny (n : Nat) : Limits := { maxDecodedStreamBytes := n }

/-- A zlib stream with one stored block holding `data` (< 65536 bytes), Adler-32 included. -/
private def storedZlib (data : List UInt8) : ByteArray :=
  let len := data.length
  let a := Flate.adler32 (B data)
  B ([0x78, 0x01, 0x01, (len % 256).toUInt8, (len / 256).toUInt8,
      ((65535 - len) % 256).toUInt8, ((65535 - len) / 256).toUInt8] ++ data ++
    [((a >>> 24) % 256).toUInt8, ((a >>> 16) % 256).toUInt8, ((a >>> 8) % 256).toUInt8,
     (a % 256).toUInt8])

/-- Fully decoded to exactly these bytes. -/
private def okData (r : Except Error Decoded) (expected : List UInt8) : Bool :=
  match r with
  | .ok (.data b) => b.data.toList == expected
  | _ => false

/-- An image placeholder with this codec and payload. -/
private def okImage (r : Except Error Decoded) (c : ImageCodec) (expected : List UInt8) :
    Bool :=
  match r with
  | .ok (.image c' _ b) => c' == c && b.data.toList == expected
  | _ => false

/-- Failure with `malformed`. -/
private def isMalformed (r : Except Error Decoded) : Bool :=
  match r with
  | .error (.malformed _ _) => true
  | _ => false

/-- Failure with `unsupported`. -/
private def isUnsupported (r : Except Error Decoded) : Bool :=
  match r with
  | .error (.unsupported _) => true
  | _ => false

/-- Failure with the per-stream limit. -/
private def isLimit (r : Except Error Decoded) : Bool :=
  match r with
  | .error (.limitExceeded .decodedStreamBytes) => true
  | _ => false

/-- Failure with the filter-count limit. -/
private def isFilterLimit (r : Except Error Decoded) : Bool :=
  match r with
  | .error (.limitExceeded .filters) => true
  | _ => false

/-- PNG "Up" rows (tag 2), 3 columns: rows `1 2 3` and `+1 +1 +1`. -/
private def pngRows : List UInt8 := [2, 1, 2, 3, 2, 1, 1, 1]

/-- `/DecodeParms` for the PNG rows. -/
private def pngParms : PdfObject := .dict [(K "Predictor", .int 12), (K "Columns", .int 3)]

-- The stored-zlib helper round-trips through Flate.
#guard decide ((Flate.flateDecode dl (storedZlib pngRows)).toOption.map (·.data.toList)
  = some pngRows)

-- No filter: unchanged; /DecodeParms ignored.
#guard okData (decodeStream dl [] (B [1, 2, 3])) [1, 2, 3]
#guard okData (decodeStream dl [(K "DecodeParms", .int 5)] (B [1, 2, 3])) [1, 2, 3]
#guard okData (decodeStream dl [(K "Filter", .array [])] (B [7])) [7]
#guard isLimit (decodeStream (tiny 2) [] (B [1, 2, 3]))

-- Flate + PNG predictor (Up).
#guard okData (decodeStream dl [(K "Filter", N "FlateDecode"), (K "DecodeParms", pngParms)]
  (storedZlib pngRows)) [1, 2, 3, 2, 3, 4]
-- Same with array forms and the abbreviation.
#guard okData (decodeStream dl [(K "Filter", .array [N "Fl"]),
  (K "DecodeParms", .array [pngParms])] (storedZlib pngRows)) [1, 2, 3, 2, 3, 4]
-- Flate without parameters: no predictor.
#guard okData (decodeStream dl [(K "Filter", N "FlateDecode")] (storedZlib [9, 8]))
  [9, 8]
-- `/DL` (task 8.10) only reserves the output: exact, too small, negative, huge, not an integer.
#guard [.int 6, .int 1, .int (-5), .int (2 ^ 40), .null].all fun v =>
  okData (decodeStream dl [(K "Filter", N "FlateDecode"), (K "DecodeParms", pngParms),
    (K "DL", v)] (storedZlib pngRows)) [1, 2, 3, 2, 3, 4] &&
  okData (decodeStreamB dl ⟨100⟩ [(K "Filter", N "FlateDecode"), (K "DL", v)]
    (storedZlib [9, 8])).1 [9, 8]
#guard declaredLength [(K "DL", .int 7)] == 7 && declaredLength [(K "DL", .int (-7))] == 0 &&
  declaredLength [] == 0
#guard flateCap dl [] 1000 3 == 1000 && flateCap dl [] (2 ^ 40) 3 == 2048 * 3 + 4096 &&
  flateCap (tiny 10) [] 1000 100 == 10 && flateCap dl [(K "Predictor", .int 12),
    (K "Columns", .int 3)] 6 100 == 6 + 6 / 3 + 1

-- ASCIIHex → Flate chain, null params for the first filter.
#guard okData (decodeStream dl [(K "Filter", .array [N "ASCIIHexDecode", N "FlateDecode"]),
  (K "DecodeParms", .array [.null, pngParms])]
  (Ascii.asciiHexEncode (storedZlib pngRows))) [1, 2, 3, 2, 3, 4]
-- ASCII85 → AHx chain.
#guard okData (decodeStream dl [(K "Filter", .array [N "A85", N "AHx"])]
  (Ascii.ascii85Encode (Ascii.asciiHexEncode (B [0xde, 0xad])))) [0xde, 0xad]

-- LZW (codes 256 65 66 65 257, 9 bits) with /EarlyChange 0 and 1; 2 is malformed.
#guard okData (decodeStream dl [(K "Filter", N "LZWDecode")] (B [128, 16, 72, 68, 24, 8]))
  [65, 66, 65]
#guard okData (decodeStream dl [(K "Filter", N "LZWDecode"),
  (K "DecodeParms", .dict [(K "EarlyChange", .int 0)])] (B [128, 16, 72, 68, 24, 8]))
  [65, 66, 65]
#guard isMalformed (decodeStream dl [(K "Filter", N "LZWDecode"),
  (K "DecodeParms", .dict [(K "EarlyChange", .int 2)])] (B [128, 16, 72, 68, 24, 8]))

-- RunLength: literal run "abc", then 'x' × 3, then EOD.
#guard okData (decodeStream dl [(K "Filter", N "RunLengthDecode")]
  (B [2, 97, 98, 99, 254, 120, 128])) [97, 98, 99, 120, 120, 120]

-- Crypt /Identity passes through; another crypt filter is unsupported (unless decryption
-- applied it and set /Name /Identity, `Crypt.markApplied`: then it is the first case).
#guard okData (decodeStream dl [(K "Filter", .array [N "Crypt", N "AHx"])] (B [52, 49, 62]))
  [0x41]
#guard isUnsupported (decodeStream dl [(K "Filter", N "Crypt"),
  (K "DecodeParms", .dict [(K "Name", N "StdCF")])] (B [1]))
-- /Crypt must be first (ISO 32000-2 §7.4.10): second or last position is malformed,
-- also when /Identity, and also twice.
#guard isMalformed (decodeStream dl [(K "Filter", .array [N "AHx", N "Crypt"])] (B [52, 49, 62]))
#guard isMalformed (decodeStream dl [(K "Filter", .array [N "Crypt", N "Crypt"])] (B [1]))
#guard isMalformed (decodeStream dl [(K "Filter", .array [N "AHx", N "Crypt", N "DCT"])]
  (B [52, 49, 62]))
#guard decide ((parseChain dl [(K "Filter", .array [N "Fl", N "Crypt"])]).toOption.isNone)
#guard decide ((parseChain dl [(K "Filter", .array [N "Crypt", N "Fl"])]).toOption.map
  List.length = some 2)
-- decodeBytes: data passes, an image codec is the caller's error.
#guard decide ((decodeBytes dl [(K "Filter", N "AHx")] (B [52, 49, 62]) (.unsupported "img")).toOption.map
  (·.data.toList) = some [0x41])
#guard (match decodeBytes dl [(K "Filter", N "DCT")] (B [1]) (.unsupported "img") with
  | .error (.unsupported "img") => true | _ => false)

-- DCT placeholder: the payload is the AHx output; codec parameters are kept.
#guard okImage (decodeStream dl [(K "Filter", .array [N "ASCIIHexDecode", N "DCTDecode"])]
  (B [70, 70, 68, 56, 62])) .dct [0xff, 0xd8]
#guard okImage (decodeStream dl [(K "Filter", N "JPXDecode")] (B [1, 2])) .jpx [1, 2]
#guard okImage (decodeStream dl [(K "Filter", N "CCF"),
  (K "DecodeParms", .dict [(K "K", .int (-1))])] (B [5])) .ccitt [5]
#guard okImage (decodeStream dl [(K "Filter", N "JBIG2Decode")] (B [])) .jbig2 []
-- A filter after an image codec is unsupported.
#guard isUnsupported (decodeStream dl [(K "Filter", .array [N "DCTDecode", N "AHx"])] (B []))

-- /Filter and /DecodeParms mismatch.
#guard isMalformed (decodeStream dl [(K "Filter", .array [N "AHx", N "Fl"]),
  (K "DecodeParms", .array [.null])] (B []))
#guard isMalformed (decodeStream dl [(K "Filter", .array [N "AHx", N "Fl"]),
  (K "DecodeParms", pngParms)] (B []))
#guard isMalformed (decodeStream dl [(K "Filter", N "AHx"),
  (K "DecodeParms", .array [.int 1])] (B []))
#guard isMalformed (decodeStream dl [(K "Filter", .int 3)] (B []))
#guard isMalformed (decodeStream dl [(K "Filter", .array [.int 3])] (B []))
#guard isUnsupported (decodeStream dl [(K "Filter", .ref 4 0)] (B []))

-- Unknown filter.
#guard isUnsupported (decodeStream dl [(K "Filter", N "Foo")] (B []))
#guard isUnsupported (decodeStream dl [(K "Filter", .array [N "AHx", N "Foo"])] (B []))

-- Too many filters (9 > limits.maxFilters = 8): limitExceeded .filters.
#guard isFilterLimit (decodeStream dl
  [(K "Filter", .array (List.replicate 9 (N "AHx")))] (B []))
-- The cap follows the limits: 3 filters with maxFilters 2; a single name with maxFilters 0.
#guard isFilterLimit (decodeStream { maxFilters := 2 }
  [(K "Filter", .array (List.replicate 3 (N "AHx")))] (B []))
#guard isFilterLimit (decodeStream { maxFilters := 0 } [(K "Filter", N "AHx")] (B []))
#guard okData (decodeStream { maxFilters := 2 } [(K "Filter", .array [N "AHx", N "AHx"])]
  (Ascii.asciiHexEncode (Ascii.asciiHexEncode (B [0x42])))) [0x42]
-- Eight is fine: AHx eight times over a hex-encoded-eight-times payload.
#guard okData (decodeStream dl [(K "Filter", .array (List.replicate 8 (N "AHx")))]
  (Nat.repeat Ascii.asciiHexEncode 8 (B [0x42]))) [0x42]

-- Bombs: nested RunLength exceeding a tiny limit is rejected.
-- Stage 1 fits (128 bytes of 129), stage 2 would expand it to 8192 bytes.
#guard isLimit (decodeStream (tiny 150) [(K "Filter", .array [N "RL", N "RL"])]
  (B [129, 129, 128]))
#guard isLimit (decodeStream (tiny 4) [(K "Filter", N "RL")] (B [251, 0, 128]))


-- Document-wide budget (task 3.10).
/-- Summary of a budgeted result: output bytes or the error kind, and the budget left. -/
private def sb (p : (Except Error Decoded) × Budget) : String :=
  let r := match p.1 with
    | .ok d => s!"ok {d.bytes.data.toList}"
    | .error (.limitExceeded k) => s!"limit {reprStr k}"
    | .error _ => "err"
  s!"{r} rem={p.2.remaining}"

/-- An `/ASCIIHexDecode` stream dictionary. -/
private def hexD : Dict := [(K "Filter", N "AHx")]
/-- 7 raw bytes `414243>`, decoding to `ABC` under `hexD`. -/
private def hexRaw : ByteArray := "414243>".toUTF8

-- Budget exactly hit: 3 decoded bytes from a budget of 3.
#guard sb (decodeStreamB dl ⟨3⟩ hexD hexRaw) == "ok [65, 66, 67] rem=0"
-- A single stream over the remaining budget: the total-budget error, charged its cap (2).
#guard sb (decodeStreamB dl ⟨2⟩ hexD hexRaw) ==
  "limit SafePdf.LimitKind.decodedTotalBytes rem=0"
-- The per-stream limit binds first: reported as such.
#guard sb (decodeStreamB (tiny 2) ⟨100⟩ hexD hexRaw) ==
  "limit SafePdf.LimitKind.decodedStreamBytes rem=98"
-- No filter: the raw bytes are charged too (B3).
#guard sb (decodeStreamB dl ⟨5⟩ [] (B [1, 2, 3])) == "ok [1, 2, 3] rem=2"
#guard sb (decodeStreamB dl ⟨2⟩ [] (B [1, 2, 3])) ==
  "limit SafePdf.LimitKind.decodedTotalBytes rem=2"
-- Parse errors are free.
#guard sb (decodeStreamB dl ⟨5⟩ [(K "Filter", N "Foo")] (B [])) == "err rem=5"
-- Unsupported /Crypt allocates nothing: not charged.
#guard sb (decodeStreamB dl ⟨5⟩ [(K "Filter", N "Crypt"),
  (K "DecodeParms", .dict [(K "Name", N "StdCF")])] (B [1])) == "err rem=5"
-- A failing Flate stage is charged its cap.
#guard sb (decodeStreamB dl ⟨50⟩ [(K "Filter", N "Fl")] (B [1, 2, 3])) == "err rem=0"
-- Intermediate stages are charged: a doubly hex-encoded byte charges the first stage's
-- output (its single hex encoding) plus the final byte.
#guard sb (decodeStreamB dl ⟨10⟩ [(K "Filter", .array [N "AHx", N "AHx"])]
  (Ascii.asciiHexEncode (Ascii.asciiHexEncode (B [0x42])))) ==
  s!"ok [66] rem={10 - (Ascii.asciiHexEncode (B [0x42])).size - 1}"
-- Many small streams exhausting a tiny total budget of 10: three fit, then the rest fail.
#guard (decodeAllB dl true ⟨10⟩ (List.replicate 5 (hexD, hexRaw))).1.map
  (fun r => match r with
    | .ok _ => "ok"
    | .error (.limitExceeded .decodedTotalBytes) => "total"
    | .error _ => "err") == ["ok", "ok", "ok", "total", "total"]
#guard (decodeAllB dl true ⟨10⟩ (List.replicate 5 (hexD, hexRaw))).2.remaining == 0
#guard ((decodeAllB dl true ⟨10⟩ (List.replicate 5 (hexD, hexRaw))).1.map okSize).sum == 9

end Tests

end SafePdf.Core.Filter
