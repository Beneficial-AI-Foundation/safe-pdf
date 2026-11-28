# Proof patterns: spec / impl / equivalence

Audience: a Lean-literate engineer who must write the next spec/impl/equivalence triple
(xref tables, filters, ...). Written after the lexer triple (task 1.6) and the object-grammar
spec and parser (tasks 1.4, 1.5). It follows Plan.md §5.1 and is the mitigation for the §9 risk
"one-person bus factor on proofs". Toolchain: Lean v4.36.0, no Mathlib, no Batteries.

Every snippet below is copied from the repo; `path:line` is where it lives at the time of
writing. Line numbers drift: search for the quoted identifier if a line no longer matches.
Anything labelled "plan" is not proved yet.

## 1. The triple

For each layer there are three artefacts, each in its own file:

| Artefact | Where | Style |
|---|---|---|
| Shared contract | `SafePdf/Core/Token.lean` | types and signatures only, no logic |
| Spec | `SafePdf/Spec/<Layer>.lean` | structural over `List UInt8` / `List Token`; slow, obviously correct |
| Impl | `SafePdf/Core/<Layer>.lean` | `ByteArray` plus position; linear time, reversed accumulators |
| Equivalence | `SafePdf/Spec/<Layer>Equiv.lean` | one theorem `impl = translate spec` and its lemmas |

### 1.1 The contract

`Token.lean` is written first, by one author, before spec and impl exist. It fixes the shared
output type (`Token`, `LexErrorKind`, `LexError`) and the two `next` signatures, so the
equivalence can be plain equality (`SafePdf/Core/Token.lean:11-27`):

```
* Spec (task 1.2), over the remaining input as a list:
  `Spec.Lex.next : List UInt8 → Except LexError (Option (Token × List UInt8))`
* Core (task 1.3), over a `ByteArray` and a position:
  `Core.Lex.next : ByteArray → Nat → Except LexError (Option (Token × Nat))`
* Equivalence (task 1.6):
  `Core.Lex.next bytes pos` agrees with `Spec.Lex.next (bytes.data.toList.drop pos)` after
  translating the remaining list to a position (`bytes.size - rest.length`) and shifting
  error offsets by `pos`.
```

Design points that made the proof tractable; copy them for the next layer:

* One token (one record, one table entry) at a time, not "the whole file". PDF cannot be
  tokenized as a whole because stream data is opaque; the same is true of most layers.
* The spec returns the *rest of the input* (a suffix), the impl returns a *position*. The two
  are related by one fixed formula, `pos = bytes.size - rest.length`.
* Errors are values with an offset. The spec's offsets are relative to the list it was given,
  the impl's are absolute; the theorem shifts by `pos`.
* The `deriving` list on shared types includes `DecidableEq`, so `t == t'` and `=` both work
  in the differential script and in the theorem (`Token.lean:86`).

### 1.2 The spec

Rules for `Spec/`:

* Structural recursion over the list wherever possible; otherwise `termination_by l.length`.
* Numbered rules in the module doc (`Spec/Lex.lean:18-33`, `Spec/Object.lean:15-31`). The impl's
  module doc repeats the same numbers (`Core/ObjParse.lean:11-24`). A reviewer can then diff
  the two lists by eye.
* Where the grammar is not a function (nesting, choice), state it twice and prove them equal:
  an **inductive relation** (the specification proper, closest to the standard) and an
  **executable spec function** (what the equivalence theorem is stated against).
  `SafePdf/Spec/Object.lean` does this:
  * relation `Parses` / `ParsesItems` / `ParsesEntries`, mutual, `fuel → input → result → rest`
    (`Spec/Object.lean:84-146`);
  * function `parse` / `parseItems` / `parseEntries` (`Spec/Object.lean:167-238`);
  * `parse_sound` and `Parses.parse_eq` give `parse_eq_ok_iff : parse F ts = .ok (o, r) ↔ Parses F ts o r`
    (`Spec/Object.lean:619`), and `parse_isError_iff` handles failure (`:625`);
  * consequences are proved on the relation, where induction is cheap: unambiguity S6
    (`Parses.unique`, `:636`), `depth_le`, `length_lt`, `canonical`.
  Proofs about the spec then transfer to the impl for free once the equivalence lands.
* The relation takes the **fuel** as an index (`Parses (f + 1) (.arrayOpen :: ts) ...`), so
  "parse succeeds with fuel F" and "the object has depth at most F" are theorems, not comments.

### 1.3 The impl

Rules for `Core/`:

* Input is `ByteArray` plus a `Nat` position; `bytes[pos]` is used only under
  `if h : pos < bytes.size`, never `!` (hygiene guard, §6).
* Measure `bytes.size - pos`, with every step advancing at least one byte
  (`Core/Lex.lean:78-86`):

```lean
def skipWs (bytes : ByteArray) (pos : Nat) (inComment : Bool) : Nat :=
  if h : pos < bytes.size then
    let b := bytes[pos]
    if inComment then skipWs bytes (pos + 1) !(b == 10 || b == 13)
    else if isWhite b then skipWs bytes (pos + 1) false
    else if b == 37 then skipWs bytes (pos + 1) true
    else pos
  else pos
termination_by bytes.size - pos
```

* Accumulators are **reversed lists** (`b :: acc`) finished with one `List.reverse`
  (`Core/Lex.lean:92-97`, `readRun`). Cheap to build, and the equivalence lemma reads
  `acc.reverse ++ ...` (§4.2).
* The top-level function is a small composition of scanners:
  `next bytes pos = tokenAt bytes (skipWs bytes pos false)` (`Core/Lex.lean:312`), where
  `tokenAt` bounds-checks and calls a plain `if` chain on the first byte (`tokenOf`). Write it
  with no `let`s in the dispatch so that `split` works on it (`Core/Lex.lean:306`).
* Prove a **progress lemma** next to the definition, because the iteration needs it:
  `Core.Lex.next_pos : next bytes pos = .ok (some (t, pos')) → pos < pos' ∧ pos' ≤ bytes.size`
  (`Core/Lex.lean:395`). The spec side has the mirror `Spec.Lex.next_consumes`.
* Whole-input drivers (`lexAll`) recurse on `bytes.size - pos`; the `decreasing_by` quotes
  the progress lemma (`Core/Lex.lean:430-439`):

```lean
def lexAll (bytes : ByteArray) : Except LexError (List Token) := go 0 []
where
  go (pos : Nat) (acc : List Token) : Except LexError (List Token) :=
    match _hn : next bytes pos with
    | .error e => .error e
    | .ok none => .ok acc.reverse
    | .ok (some (t, pos')) => go pos' (t :: acc)
  termination_by bytes.size - pos
  decreasing_by have := next_pos bytes pos t pos' _hn; omega
```

### 1.4 The equivalence theorem

Exact shape for the lexer (`SafePdf/Spec/LexEquiv.lean:741`, whole-input version `:968`):

```lean
theorem next_eq (bytes : ByteArray) (pos : Nat) :
    Core.Lex.next bytes pos =
      match Spec.Lex.next (bytes.data.toList.drop pos) with
      | .ok none => .ok none
      | .ok (some (t, rest)) => .ok (some (t, bytes.size - rest.length))
      | .error e => .error { e with offset := e.offset + pos }
```

Notes:

* No hypothesis on `pos`: past the end both sides are `ok none`. Prefer a hypothesis-free
  statement; side conditions leak into every caller.
* The `match` is the translation `tr base size` (`LexEquiv.lean:641`); inside the proofs use `tr`
  and convert once at the end (`tr_eq`, `:730`).
* For whole-input functions the statement is plain equality with no translation:
  `Core.Lex.lexAll bytes = Spec.Lex.lexAll bytes.data.toList`.
* Plan for the object parser (task 1.8, not proved): the impl lexes lazily and never sees
  lexer errors after the object's last token, so the statement is against the spec run on the
  tokens actually lexed; successes are compared exactly, failures only as "both fail"
  (`progress.md` Gotchas, "For 1.8"). Decide such "agree on what" questions in the contract,
  before proving.

## 2. Workflow

1. **Contract first.** Types and signatures in a shared file (`Token.lean`), written by whoever
   coordinates, before spec and impl authors start.
2. **Spec and impl in parallel** from the same numbered rule list. Each file's module doc
   restates the rules; neither author reads the other's code.
3. **Randomized differential check before proving anything.** `scripts/lexdiff.lean` generates
   inputs from an alphabet of PDF-significant bytes plus a few random ones, runs both sides at
   every position, and compares through the same translation as the theorem
   (`scripts/lexdiff.lean:16-22`):

```lean
def agree (b : ByteArray) (pos : Nat) : Bool :=
  let l := b.data.toList.drop pos
  match Core.Lex.next b pos, Spec.Lex.next l with
  | .ok none, .ok none => true
  | .ok (some (t, p)), .ok (some (t', r)) => t == t' && p == b.size - r.length
  | .error e, .error e' => e.kind == e'.kind && e.offset == e'.offset + pos
  | _, _ => false
```

   A disagreement found here is a spec, impl or statement bug caught before it can surface as an
   unprovable goal. The wave-6 run covered 61,500 (input, position) pairs with 0 disagreements. Run it
   with `lake env lean --run scripts/lexdiff.lean` (orchestrator only: it executes code, see §6).
   Keep it as a test once the layer is proved; it also guards the translation formula.
4. **Per-component lemmas**, one per impl scanner (§4.2).
5. **Dispatch lemma**: the first-byte `if` chain equals the spec's (`tokenAt_eq`).
6. **Main theorem**: a few lines gluing 4 and 5 (`next_eq`).
7. **Iteration lemma** for whole-input drivers (`lexAll_go_eq`, §4.8).
8. Add `#print axioms` lines (§6) and `#guard` examples for each numbered rule
   (`Core/Lex.lean:443-520` for the style).

The module doc of `LexEquiv.lean` lists the same steps as a 7-point checklist. Read it with
this document; it is the shortest summary of the pattern.

## 3. Termination and totality

No `partial def` anywhere in `Core/` or `Spec/` (guard-enforced). The patterns in use:

| Situation | Pattern | Example |
|---|---|---|
| Recursion on a list | structural | `Spec/Lex.lean:69-83` (`skipWs`/`skipComment`, mutual) |
| Recursion on a position | `termination_by bytes.size - pos` | `Core/Lex.lean:86` |
| Spec loop that needs a progress fact | `match h : f l with ...` and `have := f_consumes h`, `termination_by l.length` | `Spec/Lex.lean:517-527` |
| Nested data (arrays, dicts) | **fuel** argument from `Limits`, lexicographic measure | `Core/ObjParse.lean:151, 168` |
| Spec parser over tokens | measure `(ts.length, 0 \| 1)` (the 0/1 orders the mutual functions) | `Spec/Object.lean:200, 216` |
| Xref `/Prev` chains, page tree (to come, Plan.md §5.2) | visited set carried in the recursion, measure = unvisited count; a revisit is an error value | n/a yet |

### 3.1 Fuel for depth

Nesting depth is bounded by a fuel argument, initialised from `Limits.maxObjectDepth`
(`Core/Limits.lean:21`, `parseObject` at `Core/ObjParse.lean:222`). Entering a container needs
fuel `f + 1` and passes `f` to the members, so the measure is lexicographic in
`(fuel, bytes.size - pos)`: nesting decreases the first component, moving along a container
decreases the second.

```lean
termination_by (fuel, bytes.size - pos)
decreasing_by
  all_goals
    have := Lex.next_pos bytes pos _ _ _h
    apply Prod.Lex.right
    omega
```
(`Core/ObjParse.lean:168-173`.)

The same fuel appears as an index of the spec relation, so the theorem "a successful parse
with fuel `F` has depth at most `F`" (`parse_depth_le`, `Spec/Object.lean:643`) is the S3
resource bound. Exceeding the limit is an error value (`.limitExceeded .objectDepth`), never
a slow run.

### 3.2 The unreachable-guard trick

A loop must resume at the position the nested call returned, but that call's progress lemma
(`parseObjTok_pos`) is itself a theorem about the mutual block being defined. Proving it
inside the definition forces nested-recursion proofs. Instead the loop guards the recursive
call with the progress fact and returns an error in the other branch
(`Core/ObjParse.lean:166-167`):

```lean
        if _hr : pos < r then parseArray fuel bytes r (o :: acc)
        else .error (.malformed pos "internal: no progress")
```

The else branch is dead; `parseObjTok_pos` (`Core/ObjParse.lean:412`) proves it, and the
equivalence discharges it. The spec uses the same device with `Parses.length_lt`
(`Spec/Object.lean:211`: `if _h : r.length < rest.length + 1 then ...`). In an
equivalence or soundness proof, remember the guard is there: `simp only [hlt, ↓reduceDIte]`
(§4.7) removes it once you have `hlt`.

### 3.3 Named matches

Nested `match bs with | c :: cs => match cs with ...` breaks structural recursion in v4.36
(`progress.md` Gotchas, 1.2/1.3). The fix is `termination_by` plus *named* matches
(`match hbs : bs with`; use `_hbs` if the name is unused). See
`litBody` at `Spec/Lex.lean:135-185`. The names are also what `generalize` needs later (§4.4).

## 4. Proof techniques

### 4.1 The `restAt` bridge

One definition and four lemmas translate every array access into list structure
(`LexEquiv.lean:54-100`):

```lean
def restAt (bytes : ByteArray) (p : Nat) : List UInt8 := bytes.data.toList.drop p

theorem restAt_cons {bytes : ByteArray} {p : Nat} (h : p < bytes.size) :
    restAt bytes p = bytes[p] :: restAt bytes (p + 1)
theorem restAt_nil {bytes : ByteArray} {p : Nat} (h : bytes.size ≤ p) : restAt bytes p = []
theorem length_restAt (bytes : ByteArray) (p : Nat) : (restAt bytes p).length = bytes.size - p
theorem getElem?_eq_head? (bytes : ByteArray) (p : Nat) : bytes[p]? = (restAt bytes p).head?
```

Everything else in the equivalence is stated with `restAt bytes pos` on the spec side and
`bytes.size - rest.length` on the position side. Write these first; the next layer will reuse
them verbatim (move them to a shared `Spec/Bridge.lean` when a second user appears).

### 4.2 One lemma per scanner, by `fun_induction`

For each impl scanner `f`, prove "`f bytes pos acc` equals the spec function on
`restAt bytes pos`", by `fun_induction` on `f`, with every accumulator generalized. The
statement for `readRun` (`LexEquiv.lean:207-210`):

```lean
theorem readRun_eq (bytes : ByteArray) (pos : Nat) (acc : List UInt8) (hp : pos ≤ bytes.size) :
    Core.Lex.readRun bytes pos acc =
      (acc.reverse ++ (Spec.Lex.regularRun (restAt bytes pos)).1,
        bytes.size - (Spec.Lex.regularRun (restAt bytes pos)).2.length)
```

The shape is always: payload `acc.reverse ++ specPayload`, position
`bytes.size - specRest.length`. `fun_induction` produces one case per branch of the impl
(`case1`, `case2`, ...); name the hypotheses positionally. A typical case
(`LexEquiv.lean:181-184`, `skipWs_rest`):

```lean
  fun_induction Core.Lex.skipWs bytes pos c
  case case1 p h b ih =>
    rw [ih, restAt_cons h]
    cases hb : (bytes[p] == 10 || bytes[p] == 13) <;> simp_all [b, Spec.Lex.skipComment]
```

Order of work inside a case: rewrite with the IH, rewrite `restAt_cons h`, then let
`simp_all [b, <spec defs>, <both byte-class defs>]` close it. IH names from `fun_induction` are
unreliable (`progress.md` Gotchas): use `rename_i` when `case` naming fails. The results the
scanners need from the spec (e.g. `regularRun` splitting) go in small named lemmas
(`regularRun_reg`, `regularRun_nonreg`, `LexEquiv.lean:377-387`).

Pure list functions on both sides (`parseNumber_eq`, `readDigits_eq`) go by structural
induction on the list; no bridge needed.

### 4.3 Unfold well-founded spec functions one step at a time

`simp [litBody]` on a well-founded definition either loops or does nothing. Use the equation
lemma on the left-hand side only (`LexEquiv.lean:544-548`):

```lean
theorem litBody_open (d : Nat) (l : List UInt8) :
    Spec.Lex.litBody d (40 :: l) =
      (Spec.Lex.litBody (d + 1) l).map (fun p => (40 :: p.1, p.2)) := by
  conv => lhs; rw [Spec.Lex.litBody.eq_def]
  simp
```

Then prove one such step lemma per spec branch (`litBody_open`, `litBody_close0`,
`litBody_close`, `litBody_cr`, `litBody_other`, `LexEquiv.lean:536-578`). The case proofs of the
scanner lemmas become one-line `rw`s. `simp` equation lemmas also do not fire on functions with
overlapping patterns; `rw [f.eq_def]` always works (`progress.md` Gotchas, 1.4-1.6).

### 4.4 `generalize` before dependent matches

The spec's `match hbs : bs with` (§3.3) blocks `simp` from rewriting the discriminant. Before
unfolding, replace the list expression by a variable and keep the facts you need about it
(`LexEquiv.lean:481-488`, in `litBody_escape`):

```lean
  generalize hc : bytes[q] = c
  have g1 : bytes[q + 1]? = (restAt bytes (q + 1)).head? := getElem?_eq_head? _ _
  have r2 : restAt bytes (q + 2) = (restAt bytes (q + 1)).tail := restAt_succ _ _
  ...
  generalize hr1 : restAt bytes (q + 1) = cs at g1 r2 g2 r3 ⊢
  conv => lhs; rw [Spec.Lex.litBody.eq_def]
```

Then `cases cs` and `simp [hr1, ...]`. `tokenAt_eq` does the same for the first byte
(`generalize bytes[p] = b`, `LexEquiv.lean:660`).

### 4.5 `decide` over all 256 bytes

Byte-class facts, hex/octal arithmetic and "core and spec predicate agree" are finite. State
them with `∀ b : UInt8` and `decide` (`LexEquiv.lean:119-125`):

```lean
theorem digit_sub (b : UInt8) (h : Spec.Lex.isDigit b = true) : (b - 48).toNat = b.toNat - 48 := by
  revert b h; decide

theorem hexVal?_eq : ∀ b : UInt8, Core.Lex.hexVal? b = (Spec.Lex.hexVal b).map UInt8.ofNat := by
  decide
```

When the property has hypotheses, `revert` them first. Keep the quantified `_aux` form as the
`decide` target and derive the pointwise version from it (`hexVal_lt_aux` / `hexVal_lt`,
`LexEquiv.lean:128-131`). If the two sides' predicates are literally the same expression,
`rfl` suffices (`core_isWhite`, `:105`). `decide` does not work through `String.toUTF8`; see §5.

### 4.6 Dispatch: `by_cases` on the first byte

`tokenAt_eq` (`LexEquiv.lean:649`) states
`Core.Lex.tokenAt bytes p = tr base bytes.size (Spec.Lex.nextAt off (restAt bytes p))` under
`off + base = p`. The hypothesis is what lines up the error offsets (spec errors carry `off`,
core errors carry `p`). Proof: `unfold` both sides, rewrite with the scanner lemmas of §4.2
(`rw [hexStr_eq, nameRun_eq ..., litStr_eq ..., readRun_eq ...]`), `generalize` the byte and
the tail (§4.4), then `by_cases` on each first byte in the impl's order, `subst`, and let
`simp` evaluate both `if` chains. Keep the impl's `if` order identical to the spec's;
otherwise this proof gets much longer.

### 4.7 Reducing termination guards: `↓reduceDIte`

After `by_cases h : p < bytes.size` or `by_cases hlt : mid.length < rest.length`, reduce the
`if h :` with `simp only [h, ↓reduceDIte]` (`LexEquiv.lean:654`; `Spec/Object.lean:522, 543`).
`↓reduceIte` is the non-dependent twin. This is how the unreachable guard of §3.2 disappears.

### 4.8 Iteration: suffixes, then `fun_induction` on the loop

A spec rest is a suffix of the input, so it is `restAt` of its own position
(`LexEquiv.lean:878`):

```lean
theorem restAt_of_suffix (bytes : ByteArray) (pos : Nat) (r : List UInt8)
    (h : r <:+ restAt bytes pos) : restAt bytes (bytes.size - r.length) = r
```

Prove `next_suffix` (the spec's rest is a suffix of its input), by component suffix lemmas
(`skipWs_suffix`, `regularRun_suffix`, `litBody_suffix`, `hexBody_suffix`, ...). Then:

* Generalize the loop: `lexAll_go_eq` equates the core loop with accumulator `acc` to the
  spec `lexAll` on `restAt bytes pos`, with `acc.reverse ++ ts` and `offset + pos`
  (`LexEquiv.lean:932`).
* Do not `split` on the spec loop's dependent `match h : next l`. Prove equation lemmas for
  its three outcomes (`lexAll_of_error`, `lexAll_of_none`, `lexAll_of_some`,
  `LexEquiv.lean:902-927`) and `rw` with them.
* `fun_induction Core.Lex.lexAll.go bytes pos acc`, three cases (error, end, token); in each,
  `rcases h : Spec.Lex.next (restAt bytes pos) with e' | _ | ⟨t', r⟩` and discharge the two
  impossible shapes with `simp [tr] at hn`.

### 4.9 Hand-written `DecidableEq` for nested inductives

`deriving DecidableEq` fails on a nested inductive (a field of type `List T`) in v4.36.
Write a mutual Boolean `beq`, prove soundness and reflexivity, and build the instance
(`Core/Object.lean:196-282`, mutual blocks at `:196`, `:223`, `:259`):

```lean
instance instDecidableEq : DecidableEq PdfObject := fun a b =>
  if h : beq a b = true then isTrue (eq_of_beq a b h)
  else isFalse (fun e => h (e ▸ beq_self a))
```

`deriving BEq` and `Repr` do work. Mutual structural recursion through `List` and
`List (A × T)` needs no `termination_by` (`Core/Object.lean:196-230`). Mutual `theorem` blocks
need every member to be recursive, else "unused termination_by".

### 4.10 `rotate_left` for side goals of `rw [f]`

`rw [parseItems] at h` on a function with overlapping patterns leaves the pattern-exclusion
side goal *after* the main goal. Swap them with `rotate_left` (`swap` is Mathlib-only)
(`Spec/Object.lean:351-354`):

```lean
      · rw [parseItems] at h
        rotate_left
        · exact ht
        cases hpo : parse f (t :: rest) with
```

### 4.11 Mutual induction and `Parses`-style relations

Soundness (`parse_sound`) is proved by strong induction on the input length packaged as
`sound_aux (n : Nat) : ∀ ts, ts.length ≤ n → ...` (`Spec/Object.lean:289`); completeness is a
mutual `theorem` block by structural recursion on the derivation
(`Parses.parse_eq` / `ParsesItems.parseItems_eq` / `ParsesEntries.parseEntries_eq`,
`Spec/Object.lean:498-545`). Completeness for entries carries a generalized invariant
(`(∀ k ∈ Dict.keys es, k ∉ seen)`) for the accumulator-like parameter, exactly as
`readRun_eq` does for `acc`.

### 4.12 Performance: a value read after a call keeps it shared (task 13.1)

`Array` updates are in place only when the array is uniquely referenced. A projection of a
structure read **after** a call that consumes the structure keeps the structure alive across
the call, so the callee sees a shared value and every push copies. Instance: `Run.stepR` read
`m.oc` after `localStep env fr m s op`; `addSegs` then copied the whole path array per segment
(quadratic; 100k `l` operators took 7 s). Fix: `let moc := m.oc` before the call and use `moc`
afterwards; the result is `rfl`-equal, so no proof changes. Check: scaling run of 100k / 200k /
500k / 1M segments (time at 2n <= 2.5 x time at n) or the IR (`set_option trace.compiler.ir.result true`):
no `inc` of the machine before the call. Applies to any state-threading step function.

## 5. Lean v4.36 pitfalls

Collected from `progress.md` Gotchas; one line each. When you hit a new one, append it there.

| Pitfall | Do this instead |
|---|---|
| `if_pos`, `if_neg`, `dif_pos`, `dif_neg` deprecated | `simp`, `dite_eq_left`, `dite_eq_right`, `rw [dite_eq_left hlt]` |
| `if_false` deprecated | `ite_false` |
| `String.mk` deprecated | `String.ofList` |
| `List.forM'` missing | `forM` |
| `List.nodup_reverse` missing | `List.pairwise_reverse` |
| `conv_lhs`, `swap`, `on_goal` (Mathlib) | `conv => lhs; ...`, `rotate_left`, `case neg => ...` |
| `show` is a keyword | do not name a helper `show` |
| `deriving DecidableEq` on nested inductives | §4.9 |
| `decide` stuck on `String.toUTF8` | `#guard`, or literal byte lists, or `decide` over `∀ b : UInt8` |
| `split at h` fails behind a `let` | pass the scrutinee as a function parameter; write dispatch as a plain `if` chain (§1.3) |
| `simp [f]` on a well-founded `f` | `rw [f.eq_def]`, `conv => lhs; rw [f.eq_def]` (§4.3) |
| Nested `match` breaks structural recursion | `termination_by` and named matches (§3.3) |
| `fun_induction` IH names unreliable | `rename_i`, or name cases positionally and check |
| `simp [f]` leaves `x ≤ max x y` | `Nat.le_max_left` |
| `Except` has no `BEq` | compare via `Sum` in tests, or pattern-match |
| `ByteArray` has `DecidableEq` but no `Repr` | print `.data.toList` |
| `getElem?_neg` for `ByteArray` | works; use it to turn `bytes[i]? = none` into a bound |
| ByteArray API | `emptyWithCapacity`, `extract`, `++`, `foldl`, `push`, `bytes[i]?` work; set a byte with `⟨b.data.modify i f⟩` |
| Importing `Lean` in Shell/Core | do not; it links the compiler library into the executable |

Non-obvious positive habits:

* `simp_all [b, ...]` where `b` is a `let` (`let b := bytes[pos]`) needs `b` in the simp set.
* When a spec function uses `Nat` and the impl uses `UInt8`, prove a one-line bridge by
  `decide` (`hexVal?_eq`, `digit_sub`, `ofNat_octal_aux`, `nib_byte`, `oct3`) rather than
  fighting `UInt8` arithmetic inside the big proofs.
* When a unification goal looks hopeless, the hypothesis is usually in the wrong *shape*, not
  missing: restate the lemma over `restAt` (§4.1) or generalize an accumulator.

## 6. Hygiene

### 6.1 Forbidden constructs

`scripts/check-hygiene.sh` (python scanner `scripts/hygiene.py`) strips comments and string
literals, then greps. In `SafePdf/Core/`, `SafePdf/Spec/`, `SafePdf/Repair.lean`:
`partial`, `unsafe`, `panic!`, any `ident!` call (`get!`, `head!`, ...), `xs[i]!`, `sorry`.
Elsewhere under `SafePdf/` and `Tests/`: `sorry`.

* Use the script as the authority. A plain grep on Core module docs trips on prose that
  mentions `partial` or `sorry`.
* `s!`, `m!`, `f!` interpolation macros are exempt. An identifier that legitimately ends in
  `!` needs an allowlist entry in `scripts/hygiene.py`, with a reason.
* Index with `if h : i < xs.size then xs[i]` or `xs[i]?`.

### 6.2 The axiom gate

Top-level theorems may depend only on `propext`, `Classical.choice`, `Quot.sound`. The guard
runs `scripts/axioms.lean` and fails on anything else, including `sorryAx`. To register a
theorem, add one line per top-level theorem to `scripts/axioms.lean` (the file's header
explains this), under a comment naming the task and file:

```lean
-- Phase 1, task 1.6: lexer equivalence, C5 (SafePdf/Spec/LexEquiv.lean)
#print axioms SafePdf.Spec.LexEquiv.next_eq
#print axioms SafePdf.Spec.LexEquiv.lexAll_eq
```

(`scripts/axioms.lean` near the end.) List the main theorem, the dispatch lemma, every scanner
lemma, and every spec-side theorem that a later layer relies on. Subagents do not edit
`scripts/axioms.lean` while others are working: report the lines to add.

`check-hygiene.sh` needs a successful `lake build` first (the axiom step imports built modules).
Options: `--root DIR` scans another tree, `--no-axioms` skips the audit.

### 6.3 Checking a file while others build

* Never run `lake build`, `lake exe` or `lake env` concurrently in one checkout; concurrent
  builds are not safe (`CLAUDE.md`, "Concurrent builds"). The orchestrator builds; everyone
  else runs the **single-file check**, `lake env lean <file>` (about 0.2 s), which reads the
  already built `.olean`s of the imports and writes nothing to `.lake/`.
* The single-file check can import only modules that are already built. A new equivalence
  file that imports another new, unbuilt file cannot be checked this way; say so in the
  report, or work in a git worktree, where building is free (the project has no Lake
  dependencies).
* New files must be added by the orchestrator to `SafePdf.lean` (umbrella) and, for tests, to
  `Tests/Main.lean`. Executables that run code (`scripts/lexdiff.lean`, `lake exe tests`) are
  orchestrator-only in the shared checkout.
* Lake builds only modules that belong to a `lean_lib`; a module outside every lib fails with
  "object file ... does not exist".

## 7. When a proof is too big

The integrity rule (`CLAUDE.md`): a theorem that cannot be proved as stated is never weakened
silently, and `sorry` never lands.

1. **Never `sorry`, never an axiom, never a weaker statement under the old name.** The hygiene
   guard rejects the first two; review rejects the third.
2. **Prove everything that is complete.** Land every lemma that compiles (scanner lemmas,
   step lemmas, suffix lemmas), each with a docstring and an `#print axioms` line. Partial
   progress is real progress and the lemmas are reusable.
3. **Record the remaining statements** as exact Lean statements in the ledger (`progress.md`
   Gotchas or the task's row), with what was tried and what blocks it.
4. **Split the task** in the ledger: `1.8` into `1.8a` (components) and `1.8b` (main theorem),
   so the next wave can pick up the remainder. Report the obstacle to the human; if the
   statement itself must change (as the parser equivalence does, see §1.4), put the decision
   in the ledger's Decisions section and say what is now compared.
5. **Re-check by the cheap route first.** Before spending a day on an unprovable goal, run the
   differential script (§2 step 3) on the failing shape; a counterexample means the spec, the
   impl, or the statement is wrong, not the proof.

## TODO (after 1.7/1.8)

Sections to add when tasks 1.7 (printer and round-trip `parse (print o) = o` over
`PdfObject.Canonical`, `SafePdf/Spec/RoundTrip.lean`) and 1.8 (parser equivalence,
`SafePdf/Spec/ObjEquiv.lean`) land:

* Equivalence for a *mutual, fueled* parser: how the position measure and fuel measure line up
  with the spec's `(ts.length, 0 | 1)`, and how `parseObjTok_pos` discharges the dead guard.
* The lazy-lexing statement ("spec run on the tokens actually lexed"), and why failures are
  compared only as "both fail".
* Round-trip proofs: canonical forms, lemmas of the shape `lexAll (print o) = tokens o`, and
  how `Parses.canonical` feeds `PdfObject.Canonical`.
* Property tests against `qpdf --json` (task 1.11) and the M1 exit checklist.
