import SafePdf.Shell.App.Tcl

/-!
# Tcl quoting is injection-free (U3)

Proofs for `SafePdf/Shell/App/Tcl.lean` (task 8.2a; Plan.md §8, §10). **Copied** from the
sibling project bib-lean, `BibLean/Gui/Tcl/Lemmas.lean` (same author/organisation), with
only the namespace, this header and docstrings changed. "U3" and "Plan.md §4.2" below refer
to bib-lean's plan. The headline results:

* `parseWord_quoteList`: for every character list `l` and every `rest` at which a word
  may end (`atWordEnd rest`: empty, white space, a command terminator or
  backslash-newline), the model of Tcl's word rules reads `quoteList l ++ rest` as one
  word with value `l`, leaving `rest`.
* `parseWordStr_quote` (U3 as stated in Plan.md §4.2): `parseWordStr (quote s) =
  some (s, "")`, and `parseWord_quote_append` for any following separator and text.
* `parseCmd_render`, `parseScript_render`: a command (script) built from literal words
  parses back into exactly those words (commands).
-/

namespace SafePdf.Shell.App.Tcl

/-! ## Unfolding lemmas -/

/-- One unfolding step of `bareWord` on a non-empty input. -/
theorem bareWord_cons (acc : List Char) (c : Char) (r : List Char) :
    bareWord acc (c :: r) =
      if isSep c || isCmdEnd c then some (acc.reverse, c :: r)
      else if c == '$' || c == '[' then none
      else if c == '\\' then
        match r with
        | [] => none
        | d :: r' =>
          if d == '\n' then some (acc.reverse, c :: r)
          else match backslash d r' with
            | some (e, k) => bareWord (e :: acc) (r'.drop k)
            | none => none
      else bareWord (c :: acc) r := by
  rw [bareWord.eq_def]; rfl

/-- One unfolding step of `bracedWord` on a non-empty input. -/
theorem bracedWord_cons (depth : Nat) (acc : List Char) (c : Char) (r : List Char) :
    bracedWord depth acc (c :: r) =
      if c == '}' then
        match depth with
        | 0 => some (acc.reverse, r)
        | d + 1 => bracedWord d ('}' :: acc) r
      else if c == '{' then bracedWord (depth + 1) ('{' :: acc) r
      else if c == '\\' then
        match r with
        | [] => none
        | e :: r' =>
          if e == '\n' then bracedWord depth (' ' :: acc) (skipSpTab r')
          else bracedWord depth (e :: '\\' :: acc) r'
      else bracedWord depth (c :: acc) r := by
  rw [bracedWord.eq_def]; rfl

/-! ## Bare words -/

/-- A bare word reads the backslash escape `escChar c` back as `c`. -/
theorem bareWord_escChar (c : Char) (acc rest : List Char) :
    bareWord acc (escChar c ++ rest) = bareWord (c :: acc) rest := by
  unfold escChar
  split
  · subst_vars; simp [bareWord, isSep, isCmdEnd, backslash]
  split
  · subst_vars; simp [bareWord, isSep, isCmdEnd, backslash]
  split
  · subst_vars; simp [bareWord, isSep, isCmdEnd, backslash]
  split
  · subst_vars; simp [bareWord, isSep, isCmdEnd, backslash]
  split
  · subst_vars; simp [bareWord, isSep, isCmdEnd, backslash]
  split
  · subst_vars; simp [bareWord, isSep, isCmdEnd, backslash, isOct, octVal]
  rename_i h1 h2 h3 h4 h5 h6
  split
  · rename_i hn
    simp only [needsEsc, Bool.or_eq_true, beq_iff_eq] at hn
    simp only [List.cons_append, List.nil_append, bareWord_cons]
    have hd : c ≠ '\n' := h1
    rcases hn with ((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h <;>
      subst h <;> simp [isSep, isCmdEnd, backslash, isOct]
  · rename_i hn
    simp only [needsEsc, Bool.or_eq_true, beq_iff_eq, not_or] at hn
    simp only [List.cons_append, List.nil_append, bareWord_cons]
    simp [isSep, isCmdEnd, *]

/-- A bare word reads `l.flatMap escChar` back as `l`, up to a word end. -/
theorem bareWord_flatMap (l : List Char) (acc rest : List Char) :
    bareWord acc (l.flatMap escChar ++ rest) = bareWord (l.reverse ++ acc) rest := by
  induction l generalizing acc with
  | nil => simp
  | cons c l ih => simp [List.append_assoc, bareWord_escChar, ih]

/-- A bare word stops (with the accumulated value) at a word end. -/
theorem bareWord_atWordEnd (acc rest : List Char) (h : atWordEnd rest = true) :
    bareWord acc rest = some (acc.reverse, rest) := by
  match rest, h with
  | [], _ => simp [bareWord]
  | c :: r, h =>
    simp only [atWordEnd, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    simp only [bareWord_cons]
    rcases h with (h | h) | ⟨rfl, h⟩
    · simp [h]
    · simp [h]
    · split at h
      · simp [isSep, isCmdEnd]
      · simp at h

/-- A plain character is written as itself by the backslash fallback. -/
theorem escChar_of_plain (c : Char) (hc : plainChar c = true) : escChar c = [c] := by
  have h1 : c ≠ '\n' := by rintro rfl; revert hc; decide
  have h2 : c ≠ '\t' := by rintro rfl; revert hc; decide
  have h3 : c ≠ '\r' := by rintro rfl; revert hc; decide
  have h4 : c ≠ '\x0b' := by rintro rfl; revert hc; decide
  have h5 : c ≠ '\x0c' := by rintro rfl; revert hc; decide
  have h6 : c ≠ '\x00' := by rintro rfl; revert hc; decide
  have hn : needsEsc c = false := by
    cases h : needsEsc c
    · rfl
    · simp only [needsEsc, Bool.or_eq_true, beq_iff_eq] at h
      rcases h with ((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h <;>
        (subst h; revert hc; decide)
  simp [escChar, h1, h2, h3, h4, h5, h6, hn]

/-- The backslash fallback leaves an all-plain list unchanged. -/
theorem flatMap_escChar_of_plain (l : List Char) (h : l.all plainChar = true) :
    l.flatMap escChar = l := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp [escChar_of_plain c h.1, ih h.2]

/-! ## Braced words -/

/-- One unfolding step of `braceOK` on a non-empty input. -/
theorem braceOK_cons (d : Nat) (c : Char) (r : List Char) :
    braceOK d (c :: r) =
      if c == '}' then
        match d with
        | 0 => false
        | d' + 1 => braceOK d' r
      else if c == '{' then braceOK (d + 1) r
      else if c == '\\' then
        match r with
        | [] => false
        | e :: r' => e != '\n' && e != '\x00' && e != '\r' && braceOK d r'
      else if c == '\x00' || c == '\r' then false
      else braceOK d r := by
  rw [braceOK.eq_def]; rfl

/-- A braced word reads a `braceOK` body back exactly, up to the matching brace. -/
theorem bracedWord_braceOK : ∀ (d : Nat) (l acc rest : List Char), braceOK d l = true →
    bracedWord d acc (l ++ '}' :: rest) = some (acc.reverse ++ l, rest)
  | d, [], acc, rest, h => by
    simp [braceOK] at h; subst h; simp [bracedWord_cons]
  | d, c :: r, acc, rest, h => by
    rw [braceOK_cons] at h
    rw [List.cons_append, bracedWord_cons]
    by_cases h1 : c = '}'
    · subst h1
      cases d with
      | zero => simp at h
      | succ d =>
        simp at h ⊢
        rw [bracedWord_braceOK d r _ rest h]; simp
    by_cases h2 : c = '{'
    · subst h2
      simp at h ⊢
      rw [bracedWord_braceOK (d + 1) r _ rest h]; simp
    by_cases h3 : c = '\\'
    · subst h3
      match r, h with
      | [], h => simp at h
      | e :: r', h =>
        simp at h
        obtain ⟨he, h⟩ := h
        simp [he]
        rw [bracedWord_braceOK d r' _ rest h]; simp
    · simp [h1, h2, h3] at h ⊢
      rw [bracedWord_braceOK d r _ rest h.2]; simp

/-! ## One word -/

/-- One unfolding step of `parseWord` on a non-empty input. -/
theorem parseWord_cons (c : Char) (r : List Char) :
    parseWord (c :: r) =
      if c == '{' then
        if isExpand r then none
        else match bracedWord 0 [] r with
          | some (w, r') => if atWordEnd r' then some (w, r') else none
          | none => none
      else if c == '"' then
        match quotedWord [] r with
        | some (w, r') => if atWordEnd r' then some (w, r') else none
        | none => none
      else if atWordEnd (c :: r) then none
      else bareWord [] (c :: r) := by
  rw [parseWord.eq_def]; rfl

/-- A word starting with `escChar c` is read as a bare word. -/
theorem parseWord_escChar (c : Char) (x : List Char) :
    parseWord (escChar c ++ x) = bareWord [] (escChar c ++ x) := by
  unfold escChar
  split
  · simp [parseWord_cons, atWordEnd, isSep, isCmdEnd]
  split
  · simp [parseWord_cons, atWordEnd, isSep, isCmdEnd]
  split
  · simp [parseWord_cons, atWordEnd, isSep, isCmdEnd]
  split
  · simp [parseWord_cons, atWordEnd, isSep, isCmdEnd]
  split
  · simp [parseWord_cons, atWordEnd, isSep, isCmdEnd]
  split
  · simp [parseWord_cons, atWordEnd, isSep, isCmdEnd]
  rename_i h1 h2 h3 h4 h5 h6
  split
  · simp [parseWord_cons, atWordEnd, isSep, isCmdEnd, h1]
  · rename_i hn
    simp only [needsEsc, Bool.or_eq_true, beq_iff_eq, not_or] at hn
    simp [parseWord_cons, atWordEnd, isSep, isCmdEnd, *]

/-- A plain character is neither `{` nor `"` and never starts a word end. -/
theorem plainChar_facts (c : Char) (hc : plainChar c = true) :
    c ≠ '{' ∧ c ≠ '"' ∧ atWordEnd [c] = false ∧ ∀ x, atWordEnd (c :: x) = false := by
  have h1 : c ≠ '{' := by rintro rfl; revert hc; decide
  have h2 : c ≠ '"' := by rintro rfl; revert hc; decide
  have h3 : c ≠ '\\' := by rintro rfl; revert hc; decide
  have hs : isSep c = false := by
    cases h : isSep c
    · rfl
    · simp only [isSep, Bool.or_eq_true, beq_iff_eq] at h
      rcases h with (((h | h) | h) | h) | h <;> (subst h; revert hc; decide)
  have he : isCmdEnd c = false := by
    cases h : isCmdEnd c
    · rfl
    · simp only [isCmdEnd, Bool.or_eq_true, beq_iff_eq] at h
      rcases h with h | h <;> (subst h; revert hc; decide)
  refine ⟨h1, h2, ?_, ?_⟩
  · simp [atWordEnd, hs, he]
  · intro x; simp [atWordEnd, hs, he, h3]

/-- A brace-quoted word never looks like an argument expansion `{*}`. -/
theorem isExpand_braceOK (l rest : List Char) (hl : braceOK 0 l = true)
    (hr : atWordEnd rest = true) : isExpand (l ++ '}' :: rest) = false := by
  unfold isExpand
  split
  · rename_i r heq
    match l, heq, hl with
    | [], heq, _ => simp at heq
    | [x], heq, _ =>
      simp at heq; obtain ⟨_, rfl⟩ := heq; simp [hr]
    | x :: y :: t, heq, hl =>
      simp at heq; obtain ⟨rfl, rfl, _⟩ := heq; simp [braceOK_cons] at hl
  · rfl

/-- **U3, list form.** `quoteList l` followed by anything a word may end at is read as one
word whose value is `l`. -/
theorem parseWord_quoteList (l rest : List Char) (h : atWordEnd rest = true) :
    parseWord (quoteList l ++ rest) = some (l, rest) := by
  unfold quoteList
  split
  · rename_i hp
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hp
    obtain ⟨hne, hp⟩ := hp
    match l, hne, hp with
    | c :: r, _, hp =>
      have hc : plainChar c = true := by simp at hp; exact hp.1
      obtain ⟨h1, h2, -, h4⟩ := plainChar_facts c hc
      rw [List.cons_append, parseWord_cons]
      simp only [beq_iff_eq, h1, h2, h4, ↓reduceIte]
      have hq : bareWord [] (c :: (r ++ rest)) = bareWord [] ((c :: r).flatMap escChar ++ rest) := by
        rw [flatMap_escChar_of_plain _ hp]; rfl
      rw [hq, bareWord_flatMap, bareWord_atWordEnd _ _ h]
      simp
  split
  · rename_i _ hb
    show parseWord ('{' :: (l ++ ['}'] ++ rest)) = _
    rw [parseWord_cons]
    simp only [beq_self_eq_true, ↓reduceIte, List.append_assoc, List.cons_append,
      List.nil_append, isExpand_braceOK l rest hb h, Bool.false_eq_true]
    rw [bracedWord_braceOK 0 l [] rest hb]
    simp [h]
  · rename_i hb
    match l, hb with
    | [], hb => simp [braceOK] at hb
    | c :: r, _ =>
      rw [List.flatMap_cons, List.append_assoc, parseWord_escChar, ← List.append_assoc,
        ← List.flatMap_cons, bareWord_flatMap, bareWord_atWordEnd _ _ h]
      simp

/-- **U3.** Tcl reads `quote s`, followed by anything a word may end at (white space, a
command terminator, backslash-newline or the end of the script), as exactly one word whose
value is `s`; the rest is left unread. No command or variable substitution, no word
splitting, no backslash surprise: for every string `s`. -/
theorem parseWordStr_quote_append (s rest : String) (h : atWordEnd rest.toList = true) :
    parseWordStr (quote s ++ rest) = some (s, rest) := by
  simp [parseWordStr, quote, parseWord_quoteList _ _ h]

/-- **U3** as stated in Plan.md §4.2. -/
theorem parseWordStr_quote (s : String) : parseWordStr (quote s) = some (s, "") := by
  have := parseWordStr_quote_append s "" (by simp [atWordEnd])
  simpa using this

/-- **U3, list form with a separator.** -/
theorem parseWord_quote_sep (s : String) (sep : Char) (rest : List Char)
    (h : isSep sep || isCmdEnd sep) :
    parseWord ((quote s).toList ++ sep :: rest) = some (s.toList, sep :: rest) := by
  simp only [quote, String.toList_ofList]
  exact parseWord_quoteList _ _ (by simp [atWordEnd, h])

/-! ## Commands and scripts -/

/-- Quoting never produces the empty word. -/
theorem quoteList_ne_nil (l : List Char) : quoteList l ≠ [] := by
  unfold quoteList
  split
  · rename_i hp; intro h; subst h; simp at hp
  split
  · simp
  · rename_i hb
    match l, hb with
    | [], hb => simp [braceOK] at hb
    | c :: r, _ =>
      have : escChar c ≠ [] := by unfold escChar; repeat' split
                                  all_goals simp
      rw [List.flatMap_cons]; intro h; exact this (List.append_eq_nil_iff.mp h).1

/-- A quoted word never starts with `#` (it is never read as a comment). -/
theorem quoteList_append_ne_hash (l x t : List Char) : quoteList l ++ x ≠ '#' :: t := by
  unfold quoteList
  split
  · rename_i hp
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hp
    obtain ⟨hne, hp⟩ := hp
    match l, hne, hp with
    | c :: r, _, hp =>
      have hc : plainChar c = true := by simp at hp; exact hp.1
      intro h; simp at h; obtain ⟨rfl, -⟩ := h; revert hc; decide
  split
  · simp
  · rename_i hb
    match l, hb with
    | [], hb => simp [braceOK] at hb
    | c :: r, _ =>
      rw [List.flatMap_cons, List.append_assoc]
      unfold escChar
      split; · simp
      split; · simp
      split; · simp
      split; · simp
      split; · simp
      split; · simp
      split; · simp
      rename_i hn
      intro h; simp at h; obtain ⟨rfl, -⟩ := h; revert hn; decide

/-- When `parseWord` succeeds, the rest starts at a word end. -/
theorem parseWord_some_atWordEnd (y : List Char) (p : List Char × List Char)
    (h : parseWord y = some p) : atWordEnd y = false := by
  match y, h with
  | [], h => simp [parseWord] at h
  | c :: r, h =>
    by_cases h1 : c = '{'
    · subst h1; simp [atWordEnd, isSep, isCmdEnd]
    by_cases h2 : c = '"'
    · subst h2; simp [atWordEnd, isSep, isCmdEnd]
    rw [parseWord_cons] at h
    simp only [beq_iff_eq, h1, h2, ↓reduceIte] at h
    split at h
    · simp at h
    next hn => simpa using hn

/-- One unfolding step of `skipSep` on a non-empty input. -/
theorem skipSep_cons (c : Char) (r : List Char) :
    skipSep (c :: r) =
      if isSep c then skipSep r
      else if c == '\\' then
        match r with
        | '\n' :: r' => skipSep r'
        | _ => c :: r
      else c :: r := by
  rw [skipSep.eq_def]; rfl

/-- `skipSep` leaves an input that does not start at a word end unchanged. -/
theorem skipSep_of_atWordEnd (y : List Char) (h : atWordEnd y = false) (hne : y ≠ []) :
    skipSep y = y := by
  match y, h with
  | c :: r, h =>
    simp only [atWordEnd, Bool.or_eq_false_iff, Bool.and_eq_false_iff, beq_eq_false_iff_ne] at h
    obtain ⟨⟨hs, he⟩, hb⟩ := h
    simp only [skipSep_cons, hs, Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i hc
      simp at hc; subst hc
      rcases hb with hb | hb
      · simp at hb
      · split at hb
        · simp at hb
        · split <;> simp_all
    · rfl

/-- Skipping white space never lengthens the input. -/
theorem skipSep_length : ∀ l : List Char, (skipSep l).length ≤ l.length
  | [] => by simp [skipSep]
  | c :: r => by
    rw [skipSep_cons]
    have := skipSep_length r
    split
    · simp only [List.length_cons]; omega
    split
    · split
      · rename_i r'
        have := skipSep_length r'
        simp; omega
      · simp
    · simp

/-- A quoted word followed by a word end is neither skipped nor a terminator. -/
theorem quoteList_append_facts (l x : List Char) (hx : atWordEnd x = true) :
    skipSep (quoteList l ++ x) = quoteList l ++ x ∧
      ∃ c t, quoteList l ++ x = c :: t ∧ isCmdEnd c = false ∧ c ≠ '#' := by
  have hp := parseWord_quoteList l x hx
  have ha := parseWord_some_atWordEnd _ _ hp
  have hne : quoteList l ++ x ≠ [] := by simp [quoteList_ne_nil]
  refine ⟨skipSep_of_atWordEnd _ ha hne, ?_⟩
  match hq : quoteList l ++ x, hne with
  | c :: t, _ =>
    refine ⟨c, t, rfl, ?_, ?_⟩
    · rw [hq] at ha; simp only [atWordEnd, Bool.or_eq_false_iff] at ha; exact ha.1.2
    · rintro rfl; exact quoteList_append_ne_hash l x t hq

/-- One unfolding step of `parseCmdFrom`. -/
theorem parseCmdFrom_eq (acc : List (List Char)) (src : List Char) :
    parseCmdFrom acc src =
      match skipSep src with
      | [] => some (acc.reverse, [])
      | c :: r =>
        if isCmdEnd c then some (acc.reverse, r)
        else if acc.isEmpty && c == '#' then none
        else match parseWord (c :: r) with
          | some (w, r') =>
            if r'.length < src.length then parseCmdFrom (w :: acc) r' else none
          | none => none := by
  rw [parseCmdFrom.eq_def]; rfl

/-- The characters of a command of literal words. -/
def renderLits : List String → List Char
  | [] => []
  | [s] => quoteList s.toList
  | s :: ss => quoteList s.toList ++ ' ' :: renderLits ss

/-- The source of a list of literal words is `renderLits` of their strings. -/
theorem renderList_lits (ss : List String) :
    (Word.renderList (ss.map Word.lit)).toList = renderLits ss := by
  match ss with
  | [] => simp [Word.renderList, renderLits]
  | [s] => simp [Word.renderList, renderLits, Word.render, quote]
  | s :: t :: ss =>
    have := renderList_lits (t :: ss)
    simp only [List.map_cons] at this ⊢
    simp [Word.renderList, renderLits, Word.render, quote, this]

/-- Rendered literal words followed by a newline are the first quoted word followed by a word end. -/
theorem renderLits_append (t : String) (ss : List String) (rest : List Char) :
    ∃ x, atWordEnd x = true ∧ renderLits (t :: ss) ++ '\n' :: rest = quoteList t.toList ++ x := by
  match ss with
  | [] => exact ⟨'\n' :: rest, by simp [atWordEnd, isCmdEnd], by simp [renderLits]⟩
  | u :: ss => exact ⟨' ' :: (renderLits (u :: ss) ++ '\n' :: rest), by simp [atWordEnd, isSep],
      by simp [renderLits]⟩

/-- `skipSep` leaves rendered literal words followed by a newline unchanged. -/
theorem skipSep_renderLits (t : String) (ss : List String) (rest : List Char) :
    skipSep (renderLits (t :: ss) ++ '\n' :: rest) = renderLits (t :: ss) ++ '\n' :: rest := by
  obtain ⟨x, hx, he⟩ := renderLits_append t ss rest
  rw [he]; exact (quoteList_append_facts _ _ hx).1

/-- One word, then the rest of the command. -/
theorem parseCmdFrom_word (acc : List (List Char)) (l : List Char) (s : String)
    (x : List Char) (hx : atWordEnd x = true) (hl : skipSep l = quoteList s.toList ++ x) :
    parseCmdFrom acc l = parseCmdFrom (s.toList :: acc) x := by
  obtain ⟨-, c, t, hq, he, hh⟩ := quoteList_append_facts s.toList x hx
  have hlen := skipSep_length l
  rw [parseCmdFrom_eq acc l, hl, hq]
  have hlt : x.length < l.length := by
    rw [hl] at hlen; have := quoteList_ne_nil s.toList
    cases h : quoteList s.toList with
    | nil => exact absurd h this
    | cons _ _ => simp [h] at hlen; omega
  simp only [he, Bool.false_eq_true, ↓reduceIte]
  rw [← hq, parseWord_quoteList _ _ hx]
  simp [hlt, hh]

/-- `parseCmdFrom` reads rendered literal words back one by one. -/
theorem parseCmdFrom_lits (s : String) (ss : List String) (rest : List Char) :
    ∀ (acc : List (List Char)) (l : List Char),
      skipSep l = renderLits (s :: ss) ++ '\n' :: rest →
      parseCmdFrom acc l = some (acc.reverse ++ (s :: ss).map String.toList, rest) := by
  induction ss generalizing s with
  | nil =>
    intro acc l hl
    rw [parseCmdFrom_word acc l s ('\n' :: rest) (by simp [atWordEnd, isCmdEnd]) hl,
      parseCmdFrom_eq _ _]
    simp [skipSep_cons, isSep, isCmdEnd]
  | cons t ss ih =>
    intro acc l hl
    have hx : atWordEnd (' ' :: (renderLits (t :: ss) ++ '\n' :: rest)) = true := by
      simp [atWordEnd, isSep]
    rw [parseCmdFrom_word acc l s _ hx (by rw [hl]; simp [renderLits])]
    rw [ih t (s.toList :: acc)]
    · simp
    · rw [skipSep_cons]; simp [isSep, skipSep_renderLits]

/-- A command of literal words, at the character level, parses back into its words. -/
theorem parseCmd_renderLits (ss : List String) (rest : List Char) :
    parseCmd (renderLits ss ++ '\n' :: rest) = some (ss.map String.toList, rest) := by
  unfold parseCmd
  match ss with
  | [] => rw [parseCmdFrom_eq _ _]; simp [renderLits, skipSep_cons, isSep, isCmdEnd]
  | s :: ss =>
    rw [parseCmdFrom_lits s ss rest [] _ (by simp [skipSep_renderLits])]
    simp

/-- **Commands.** A command of literal words, followed by its terminator, parses back into
exactly those words. -/
theorem parseCmd_render (ss : List String) (rest : String) :
    parseCmd ((Cmd.ofStrings ss).render ++ "\n" ++ rest).toList =
      some (ss.map String.toList, rest.toList) := by
  simp only [parseCmd, Cmd.render, Cmd.ofStrings, String.toList_append, renderList_lits]
  match ss with
  | [] => rw [parseCmdFrom_eq _ _]; simp [renderLits, skipSep_cons, isSep, isCmdEnd]
  | s :: ss =>
    rw [parseCmdFrom_lits s ss rest.toList [] _ (by simp [skipSep_renderLits])]
    simp

/-- One unfolding step of `parseScript`. -/
theorem parseScript_eq (l : List Char) :
    parseScript l =
      if l.isEmpty then some []
      else
        match parseCmd l with
        | some (ws, r) =>
          if r.length < l.length then (parseScript r).map (ws :: ·) else none
        | none => none := by
  rw [parseScript.eq_def]; rfl

/-- Characters of a rendered script of literal commands. -/
theorem render_ofStrings_toList (sss : List (List String)) :
    (Script.ofStrings sss).render.toList =
      (sss.map fun ss => renderLits ss ++ ['\n']).flatten := by
  induction sss with
  | nil => simp [Script.ofStrings, Script.render]
  | cons ss sss ih =>
    simp only [Script.ofStrings, Script.render, List.map_cons, String.join_cons,
      String.toList_append] at ih ⊢
    rw [ih]
    simp [Cmd.render, Cmd.ofStrings, renderList_lits]

/-- **Scripts.** A script of commands of literal words parses back into exactly those
commands and words. -/
theorem parseScript_render (sss : List (List String)) :
    parseScript (Script.ofStrings sss).render.toList =
      some (sss.map fun ss => ss.map String.toList) := by
  rw [render_ofStrings_toList]
  induction sss with
  | nil => simp [parseScript_eq]
  | cons ss sss ih =>
    rw [parseScript_eq]
    simp only [List.map_cons, List.flatten_cons, List.append_assoc, List.cons_append,
      List.nil_append, parseCmd_renderLits]
    simp [ih]; omega

/-! ## No raw NUL reaches Tcl -/

/-- A `braceOK` list contains no NUL character. -/
theorem nul_not_mem_of_braceOK : ∀ (d : Nat) (l : List Char), braceOK d l = true →
    '\x00' ∉ l
  | _, [], _ => by simp
  | d, c :: r, h => by
    rw [braceOK_cons] at h
    by_cases h1 : c = '}'
    · subst h1
      cases d with
      | zero => simp at h
      | succ d => simp at h; have := nul_not_mem_of_braceOK d r h; simp_all
    by_cases h2 : c = '{'
    · subst h2; simp at h; have := nul_not_mem_of_braceOK (d + 1) r h; simp_all
    by_cases h3 : c = '\\'
    · subst h3
      match r, h with
      | [], h => simp at h
      | e :: r', h =>
        simp at h
        obtain ⟨he, h⟩ := h
        have := nul_not_mem_of_braceOK d r' h
        simp only [List.mem_cons, not_or]
        refine ⟨by decide, ?_, this⟩
        intro h0; subst h0; simp at he
    · simp [h1, h2, h3] at h
      have := nul_not_mem_of_braceOK d r h.2
      simp only [List.mem_cons, not_or]
      exact ⟨fun h0 => h.1.1 h0.symm, this⟩

/-- The backslash fallback never emits a raw NUL character. -/
theorem nul_not_mem_escChar (c : Char) : '\x00' ∉ escChar c := by
  unfold escChar
  repeat' split
  all_goals (intro h0; simp [eq_comm] at h0; try simp_all)

/-- `quote` never writes a raw NUL into a script (a NUL is written `\000`), so how
`Tcl_EvalEx` treats a NUL byte in its input never matters. -/
theorem nul_not_mem_quoteList (l : List Char) : '\x00' ∉ quoteList l := by
  unfold quoteList
  split
  · rename_i hp
    simp only [Bool.and_eq_true, List.all_eq_true] at hp
    intro h; have := hp.2 _ h; revert this; decide
  split
  · rename_i hb
    have := nul_not_mem_of_braceOK 0 l hb
    simp [this]
  · simp only [List.mem_flatMap, not_exists, not_and]
    intro c _; exact nul_not_mem_escChar c

end SafePdf.Shell.App.Tcl
