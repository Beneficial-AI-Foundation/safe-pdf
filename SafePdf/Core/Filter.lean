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
  At most `maxFilters` = 8 filters, else `Error.unsupported` (no `LimitKind` fits; see the
  constant). An indirect `/Filter` or `/DecodeParms` (or array element) is
  `Error.unsupported`: the caller resolves references before calling (no resolver here).
* F3. Parameters. With no filter, `/DecodeParms` is ignored. Otherwise absent/`null` means
  "all defaults"; a dictionary is allowed only for exactly one filter; an array must have
  exactly as many elements as there are filters, each a dictionary or `null`. Anything else
  is `Error.malformed`.
* F4. Byte filters. `/FlateDecode` and `/LZWDecode` are followed by the predictor of their
  parameters (`Filter.Predictor`, ISO 32000-2 Table 10); `/LZWDecode` reads `/EarlyChange`.
  `/ASCIIHexDecode`, `/ASCII85Decode`, `/RunLengthDecode` take no parameters. `/Crypt` with
  `/Name /Identity` (the default) passes the data through; any other crypt filter is
  `Error.unsupported` (decryption is task 4.3b).
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

Per-document accounting against `Limits.maxDecodedTotalBytes` is **not** done here: this
module decodes one stream. The aggregate bound it does give is `produced_le`: the bytes
allocated by all stages of one chain are at most `(number of stages) · maxDecodedStreamBytes`,
so at most `maxFilters · maxDecodedStreamBytes` (`produced_le_maxFilters`).

## Theorems

* Totality by construction: the only recursion is structural on lists.
* `decodeStream_size_le`: the returned bytes are within `limits.maxDecodedStreamBytes`.
* `decodeStream_nil`: no `/Filter` ⇒ the data is returned unchanged (within the limit).
* `applyStages_image` / `decodeStream_image`: placeholder law — a chain `pre ++ [codec]`
  returns `.image codec parms b` where `.data b` is what `pre` decodes to.
* `decodeStream_unknown`: an unknown filter name gives `Error.unsupported`.
* `parseChain_length_le`, `produced_le`, `produced_le_maxFilters`: the aggregate bound.
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
  /-- `/Crypt` (only `/Identity` is supported here). -/
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

/-- Cap on the number of filters in one chain (F2). Real files use at most 2–3. It should
become a `Limits` field (with a `LimitKind`); until then exceeding it is `unsupported`. -/
def maxFilters : Nat := 8

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

/-- The `/Filter` names in order (F2), at most `maxFilters`. -/
def filterNames (d : Dict) : Except Error (List Name) :=
  match d.get? (Name.ofString "Filter") with
  | none => .ok []
  | some (.name n) => .ok [n]
  | some (.array items) =>
    if items.length ≤ maxFilters then namesOf items
    else .error (.unsupported s!"/Filter: more than {maxFilters} filters")
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

/-- Parse the filter chain of a stream dictionary (F1–F3). -/
def parseChain (d : Dict) : Except Error (List Stage) :=
  match filterNames d with
  | .error e => .error e
  | .ok [] => .ok []
  | .ok names =>
    match kindsOf names with
    | .error e => .error e
    | .ok kinds =>
      match parmsList d kinds.length with
      | .error e => .error e
      | .ok ps => .ok (List.zipWith Stage.mk kinds ps)

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
    else .error (.unsupported s!"/Crypt filter /{nameText n} (decryption: task 4.3b)")
  | some _ => .error (.malformed 0 "/Crypt /DecodeParms /Name is not a name")

/-- Decode one byte stage (F4). -/
def decodeOne (limits : Limits) (strict : Bool) (f : ByteFilter) (parms : Dict)
    (b : ByteArray) : Except Error ByteArray :=
  match f with
  | .flate =>
    match Flate.flateDecode limits b strict with
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

/-- Run the stages in order (F5, F6). Structural on the list. -/
def applyStages (limits : Limits) (strict : Bool) : List Stage → ByteArray →
    Except Error Decoded
  | [], b =>
    if b.size ≤ limits.maxDecodedStreamBytes then .ok (.data b) else .error limitErr
  | ⟨.image c, p⟩ :: [], b =>
    if b.size ≤ limits.maxDecodedStreamBytes then .ok (.image c p b) else .error limitErr
  | ⟨.image _, _⟩ :: _ :: _, _ => .error (.unsupported "a filter after an image codec")
  | ⟨.byte f, p⟩ :: rest, b =>
    match decodeOne limits strict f p b with
    | .error e => .error e
    | .ok o => applyStages limits strict rest o

/-- **Entry point.** Decode a stream's data `raw` with the filter chain of its dictionary
`d` (ISO 32000-2 §7.3.8, §7.4). Strict by default (F7). -/
def decodeStream (limits : Limits) (d : Dict) (raw : ByteArray) (strict : Bool := true) :
    Except Error Decoded :=
  match parseChain d with
  | .error e => .error e
  | .ok stages => applyStages limits strict stages raw

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
  unfold decodeStream at h
  split at h
  · cases h
  · exact applyStages_size_le limits strict _ raw r h

/-- With no `/Filter` there are no stages. -/
theorem parseChain_nil {d : Dict} (h : d.get? (Name.ofString "Filter") = none) :
    parseChain d = .ok [] := by
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
    (hc : parseChain d = .ok (pre ++ [⟨.image c, p⟩]))
    (hp : applyStages limits strict pre raw = .ok (.data b)) :
    decodeStream limits d raw strict = .ok (.image c p b) := by
  simp only [decodeStream, hc]
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
    {ns : List Name} (hf : filterNames d = .ok ns) (hu : ∃ n ∈ ns, kindOfName n = none) :
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
    (hk : kindOfName n = none) :
    ∃ msg, decodeStream limits d raw strict = .error (.unsupported msg) :=
  decodeStream_unknown (ns := [n]) (by simp [filterNames, hf]) ⟨n, by simp, hk⟩

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

/-- At most `maxFilters` names. -/
theorem filterNames_length_le {d : Dict} {ns : List Name} (h : filterNames d = .ok ns) :
    ns.length ≤ maxFilters := by
  unfold filterNames at h
  split at h
  · simp only [Except.ok.injEq] at h; subst h; simp [maxFilters]
  · simp only [Except.ok.injEq] at h; subst h; simp [maxFilters]
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

/-- **Chain length**: a parsed chain has at most `maxFilters` stages. -/
theorem parseChain_length_le {d : Dict} {stages : List Stage} (h : parseChain d = .ok stages) :
    stages.length ≤ maxFilters := by
  cases hn : filterNames d with
  | error e => simp [parseChain, hn] at h
  | ok names =>
    have hl := filterNames_length_le hn
    cases names with
    | nil =>
      simp only [parseChain, hn, Except.ok.injEq] at h; subst h; simp [maxFilters]
    | cons n ns =>
      simp only [parseChain, hn] at h
      cases hk : kindsOf (n :: ns) with
      | error e => simp [hk] at h
      | ok kinds =>
        cases hp : parmsList d kinds.length with
        | error e => simp [hk, hp] at h
        | ok ps =>
          simp only [hk, hp, Except.ok.injEq] at h; subst h
          rw [List.length_zipWith, kindsOf_length _ _ hk]
          exact Nat.le_trans (Nat.min_le_left _ _) hl

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
`maxFilters · maxDecodedStreamBytes` bytes. -/
theorem produced_le_maxFilters {limits : Limits} {strict : Bool} {d : Dict}
    {stages : List Stage} (h : parseChain d = .ok stages) (b : ByteArray) :
    produced limits strict stages b ≤ maxFilters * limits.maxDecodedStreamBytes :=
  Nat.le_trans (produced_le limits strict stages b)
    (Nat.mul_le_mul_right _ (parseChain_length_le h))

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

-- Crypt /Identity passes through; another crypt filter is unsupported.
#guard okData (decodeStream dl [(K "Filter", .array [N "Crypt", N "AHx"])] (B [52, 49, 62]))
  [0x41]
#guard isUnsupported (decodeStream dl [(K "Filter", N "Crypt"),
  (K "DecodeParms", .dict [(K "Name", N "StdCF")])] (B [1]))

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

-- Too many filters (9 > maxFilters).
#guard isUnsupported (decodeStream dl
  [(K "Filter", .array (List.replicate 9 (N "AHx")))] (B []))
-- Eight is fine: AHx eight times over a hex-encoded-eight-times payload.
#guard okData (decodeStream dl [(K "Filter", .array (List.replicate 8 (N "AHx")))]
  (Nat.repeat Ascii.asciiHexEncode 8 (B [0x42]))) [0x42]

-- Bombs: nested RunLength exceeding a tiny limit is rejected.
-- Stage 1 fits (128 bytes of 129), stage 2 would expand it to 8192 bytes.
#guard isLimit (decodeStream (tiny 150) [(K "Filter", .array [N "RL", N "RL"])]
  (B [129, 129, 128]))
#guard isLimit (decodeStream (tiny 4) [(K "Filter", N "RL")] (B [251, 0, 128]))

end Tests

end SafePdf.Core.Filter
