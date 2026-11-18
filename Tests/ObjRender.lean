import SafePdf

/-!
# Stable object rendering for golden tests (task 1.10)

A small, test-only pretty-printer for `PdfObject`, `Stream` and `IndirectObject`. It is
deliberately independent of the Core printer (task 1.7): golden files must describe what the
parser produced, not what the printer would emit.

Format, one line per value, two spaces of indentation per nesting level:
* `null`, `bool true`, `int -3`, `real <mantissa>e-<scale>` (the exact `Decimal`),
  `ref <num> <gen> R`;
* `string (<len>) <hex>` — strings always as hex of their decoded bytes;
* `name /<bytes>` — printable regular ASCII bytes as-is, every other byte (and `#`) as `#xx`;
* `array (<n>)` then its members, indented;
* `dict (<n>)` then one line per entry `<key>: <value>`, nested values indented.
-/

namespace SafePdf.Tests.ObjRender

open SafePdf

/-- Two lowercase hex digits of a byte. -/
def hexByte (b : UInt8) : String :=
  let digits := "0123456789abcdef".toList
  String.ofList [digits[(b >>> 4).toNat]?.getD '?', digits[(b &&& 15).toNat]?.getD '?']

/-- Hex of a byte list. -/
def hexBytes (bs : List UInt8) : String := String.join (bs.map hexByte)

/-- Whether a byte is printed literally inside a name: printable ASCII that is not a PDF
delimiter, whitespace or `#`. -/
def nameLiteral (b : UInt8) : Bool :=
  0x21 ≤ b && b ≤ 0x7e && !"()<>[]{}/%#".toUTF8.toList.contains b

/-- A name as `/…` with `#xx` escapes. -/
def renderName (n : Name) : String :=
  "/" ++ String.join (n.bytes.map fun b =>
    if nameLiteral b then (Char.ofNat b.toNat).toString else "#" ++ hexByte b)

/-- A decimal as `<mantissa>e-<scale>` (exact; no float conversion). -/
def renderDecimal (d : Decimal) : String := s!"{d.mantissa}e-{d.scale}"

/-- Indentation of `n` levels. -/
def ind (n : Nat) : String := String.ofList (List.replicate (2 * n) ' ')

mutual

/-- Lines of `o` at indentation `lvl`, the first line prefixed by `pre` (a dict key). -/
def renderObj (lvl : Nat) (pre : String) : PdfObject → List String
  | .null => [ind lvl ++ pre ++ "null"]
  | .bool b => [ind lvl ++ pre ++ s!"bool {b}"]
  | .int i => [ind lvl ++ pre ++ s!"int {i}"]
  | .real d => [ind lvl ++ pre ++ "real " ++ renderDecimal d]
  | .string s => [ind lvl ++ pre ++ s!"string ({s.length}) <{hexBytes s}>"]
  | .name n => [ind lvl ++ pre ++ "name " ++ renderName n]
  | .ref n g => [ind lvl ++ pre ++ s!"ref {n} {g} R"]
  | .array xs => (ind lvl ++ pre ++ s!"array ({xs.length})") :: renderList (lvl + 1) xs
  | .dict es => (ind lvl ++ pre ++ s!"dict ({es.length})") :: renderDict (lvl + 1) es

/-- Lines of array members. -/
def renderList (lvl : Nat) : List PdfObject → List String
  | [] => []
  | x :: xs => renderObj lvl "" x ++ renderList lvl xs

/-- Lines of dictionary entries. -/
def renderDict (lvl : Nat) : List (Name × PdfObject) → List String
  | [] => []
  | (k, v) :: es => renderObj lvl (renderName k ++ ": ") v ++ renderDict lvl es

end

/-- Most stream-data bytes shown in hex. -/
def maxDataShown : Nat := 64

/-- Lines of an indirect object. -/
def renderIndirect (io : IndirectObject) : List String :=
  match io.body with
  | .obj o => s!"object {io.num} {io.gen}" :: renderObj 1 "" o
  | .stream s =>
    let shown := s.data.toList.take maxDataShown
    let more := if s.data.size > maxDataShown then " …" else ""
    (s!"stream {io.num} {io.gen}" :: renderObj 1 "dict: " (.dict s.dict)) ++
      [ind 1 ++ s!"data ({s.data.size}) <{hexBytes shown}>{more}"]

/-- Join lines, each terminated by a newline. -/
def unlines (ls : List String) : String := String.join (ls.map (· ++ "\n"))

end SafePdf.Tests.ObjRender
