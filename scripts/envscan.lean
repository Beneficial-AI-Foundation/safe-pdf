/-
Environment scan (Plan.md section 3 rule 3 and section 4 S1-S4, task 13.9), run by
`scripts/check-hygiene.sh` after `scripts/axioms.lean`:

    lake env lean --run scripts/envscan.lean MODULE...

The module names are the strict modules, printed by `python3 -I scripts/hygiene.py modules`
(`Core/`, `Spec/`, `Repair`, `Api`, `Quarantine/`, `Shell/Worker/Protocol`), so the source scan
and this scan share one list.  The scan imports exactly those modules from the built `.olean`s
(`lake build` first) and inspects every constant they define, definitions as well as theorems:

* the axioms a constant depends on are within `propext`, `Classical.choice`, `Quot.sound`
  (so no `sorryAx`, no `Lean.ofReduceBool`/`native_decide`, no user axiom);
* no `axiom` declaration;
* no `@[extern]`, no `@[implemented_by]` (except `T.ctorIdx`, implemented by the generated
  `T.ctorIdx._impl`);
* no `unsafe` (or `partial`-safety) constant except the compiler-generated `T.ctorIdx._impl` and the `_unsafe_rec`
  twin of a terminating definition (how well-founded recursion compiles);
* no `partial` (an opaque constant with an `_unsafe_rec` twin);
* no `IO`, `BaseIO`, `EIO`, `ST`, `EST` in a type or in a definition body, except the entries of
  `ioAllowed` below (each with its reason).

It prints the counts and exits 1 when anything is found.  `ENVSCAN_LIB` (optional) names an extra
directory searched for `.olean`s first; the guard's self-test uses it for the fixtures.  This file
is outside the library and is never imported.
-/
import Lean
open Lean

/-- Constants of a strict module that may mention `IO` (the optional file helper of the library
facade; `Api.lean` documents it as the only `IO` of the module). -/
def ioAllowed : List Name := [`SafePdf.Api.openFile]

/-- Names whose occurrence in a type or body is the forbidden effect (S4). -/
def ioNames : List Name := [`IO, `BaseIO, `EIO, `ST, `EST]

def mentionsIO (e : Expr) : Bool :=
  (e.find? fun x => x.isConst && ioNames.contains x.constName!).isSome

/-- Constants a constant's declaration refers to (type, value, constructors). -/
def refs (ci : ConstantInfo) : Array Name :=
  let ns := ci.type.getUsedConstants
  let ns := match ci with
    | .defnInfo v => ns ++ v.value.getUsedConstants
    | .thmInfo v => ns ++ v.value.getUsedConstants
    | .opaqueInfo v => ns ++ v.value.getUsedConstants
    | .inductInfo v => ns ++ v.ctors.toArray
    | .ctorInfo v => ns.push v.induct
    | .recInfo v => ns ++ v.all.toArray
    | _ => ns
  ns

/-- Axioms a constant depends on, memoised over the whole environment. -/
partial def axiomsOf (env : Environment) (n : Name) :
    StateM (Std.HashMap Name NameSet) NameSet := do
  if let some s := (← get)[n]? then return s
  -- cut recursion on self-references (recursors, inductive types and constructors)
  modify (·.insert n {})
  let some ci := env.find? n | return {}
  let mut acc : NameSet := {}
  if let .axiomInfo _ := ci then acc := acc.insert n
  for r in refs ci do
    if r != n then
      acc := (← axiomsOf env r).foldl (·.insert ·) acc
  modify (·.insert n acc)
  return acc

def allowedAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

def main (mods : List String) : IO UInt32 := do
  if mods.isEmpty then
    IO.eprintln "envscan: no modules given (use scripts/check-hygiene.sh)"
    return 2
  let extra := match (← IO.getEnv "ENVSCAN_LIB") with
    | some d => [System.FilePath.mk d]
    | none => []
  initSearchPath (← findSysroot) extra
  let names := mods.map String.toName
  let env ← try importModules (names.toArray.map fun m => {module := m}) {} 0
    catch e =>
      IO.eprintln s!"envscan: cannot import the strict modules ({e}); run `lake build` first"
      return 2
  let strict : NameSet := names.foldl (·.insert ·) {}
  let mut bad : Array String := #[]
  let mut defs := 0
  let mut thms := 0
  let mut other := 0
  let mut impls := 0
  let mut twins := 0
  let mut partials := 0
  let mut memo : Std.HashMap Name NameSet := {}
  for (nm, ci) in env.constants.map₁.toList do
    let some mi := env.getModuleIdxFor? nm | continue
    let mn := env.header.moduleNames[mi.toNat]!
    unless strict.contains mn do continue
    let at_ := s!"{nm} ({mn})"
    match ci with
    | .thmInfo _ => thms := thms + 1
    | .defnInfo _ => defs := defs + 1
    | _ => other := other + 1
    if let .axiomInfo _ := ci then
      bad := bad.push s!"{at_}: axiom declaration"
    -- axioms of the constant
    let (axs, memo') := (axiomsOf env nm).run memo
    memo := memo'
    let extraAx := axs.toList.filter (!allowedAxioms.contains ·)
    unless extraAx.isEmpty do
      bad := bad.push s!"{at_}: depends on disallowed axiom(s): {", ".intercalate (extraAx.map toString)}"
    if isExtern env nm then
      bad := bad.push s!"{at_}: @[extern]"
    -- partial: an opaque constant with an `_unsafe_rec` twin
    let isPartial := (match ci with | .opaqueInfo _ => true | _ => false)
      && env.contains (nm ++ `_unsafe_rec)
    if isPartial then
      partials := partials + 1
      bad := bad.push s!"{at_}: partial"
    else if let some tgt := Compiler.getImplementedBy? env nm then
      -- `T.ctorIdx` is compiled through the generated `T.ctorIdx._impl`
      unless nm.getString! == "ctorIdx" && tgt == nm ++ `_impl do
        bad := bad.push s!"{at_}: @[implemented_by] {tgt}"
    if ci.isUnsafe || ci.isPartial then
      let isIdx := nm.getString! == "_impl" && nm.getPrefix.getString! == "ctorIdx"
      let base := nm.getPrefix
      let isTwin := nm.getString! == "_unsafe_rec" && env.contains base
      if isIdx then impls := impls + 1
      else if isTwin then
        twins := twins + 1
        -- the twin of a `partial` is reported at the opaque constant
      else bad := bad.push s!"{at_}: unsafe"
    unless ioAllowed.contains nm do
      let inBody := match ci with
        | .defnInfo v => mentionsIO v.value
        | _ => false
      if mentionsIO ci.type || inBody then
        bad := bad.push s!"{at_}: IO/BaseIO/EIO/ST in a type"
  -- every module must have been seen (a module without constants would hide a typo)
  IO.println s!"envscan: {mods.length} strict modules, {defs} definitions, {thms} theorems, {other} other constants (inductives, constructors, recursors, opaque)"
  IO.println s!"envscan: {impls} ctorIdx._impl, {twins} _unsafe_rec twins (terminating definitions), {partials} partial"
  let sorted := bad.qsort (· < ·)
  for b in sorted do IO.println s!"envscan: {b}"
  if sorted.isEmpty then
    IO.println "hygiene: environment scan OK"
    return 0
  IO.eprintln s!"envscan: {sorted.size} violation(s)"
  return 1
