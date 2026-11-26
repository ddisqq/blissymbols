/-!
# Blissymbols as data: structure and resolution

A Blissymbol *character* is built from positioned *shapes*, shapes from
other shapes and from primitive *paths* (lines, arcs, circles, dots, text),
and a *word* is a sequence of characters and other words.

Shapes and characters are held together in one list of **items**. If every
item refers only to items that come before it, there can be no circular
definitions and every character resolves, by a terminating recursion, into
a list of positioned primitive paths (`flatten`). That list is what a
renderer needs, in two or in three dimensions.
-/

namespace Bliss

/-- A part of an item: a primitive path or an earlier item, at an offset
(in thousandths of a unit). -/
inductive Ref
  | prim (p : Nat) (x y : Int)
  | item (j : Nat) (x y : Int)
  deriving Repr

/-- A shape or a character: positioned parts. -/
abbrev Item := List Ref

/-- A positioned primitive path. -/
structure Stroke where
  prim : Nat
  x : Int
  y : Int
  deriving Repr, DecidableEq

/-- A character of the database. -/
structure CharEntry where
  name : String
  item : Nat
  w : Int
  h : Int
  deriving Repr

/-- A part of a word: a character or an earlier word. -/
inductive WRef
  | char (c : Nat)
  | word (w : Nat)
  deriving Repr

/-! ### Well-formedness -/

/-- A part of item `i` is admissible: primitives exist, and items referred
to come earlier. -/
def Ref.ok (nPrim i : Nat) : Ref → Bool
  | .prim p _ _ => decide (p < nPrim)
  | .item j _ _ => decide (j < i)

/-- Every item in the list, numbered from `k`, has only admissible parts. -/
def wfFrom (nPrim : Nat) : Nat → List Item → Bool
  | _, [] => true
  | k, it :: rest => it.all (Ref.ok nPrim k) && wfFrom nPrim (k + 1) rest

theorem wfFrom_get {nPrim : Nat} : ∀ {k : Nat} {l : List Item},
    wfFrom nPrim k l = true → ∀ (i : Nat) (hi : i < l.length),
      ∀ r ∈ l[i], Ref.ok nPrim (k + i) r = true
  | _, [], _, _, hi => absurd hi (Nat.not_lt_zero _)
  | k, it :: rest, h, 0, _ => by
    intro r hr
    have h' := (Bool.and_eq_true_iff.1 h).1
    exact List.all_eq_true.1 h' r hr
  | k, it :: rest, h, i + 1, hi => by
    intro r hr
    have h' := (Bool.and_eq_true_iff.1 h).2
    have := wfFrom_get h' i (Nat.lt_of_succ_lt_succ hi) r hr
    have e : k + 1 + i = k + (i + 1) := by omega
    rw [← e]
    exact this

/-- The same for words. -/
def WRef.ok (nChar i : Nat) : WRef → Bool
  | .char c => decide (c < nChar)
  | .word w => decide (w < i)

def wwfFrom (nChar : Nat) : Nat → List (String × List WRef) → Bool
  | _, [] => true
  | k, w :: rest => w.2.all (WRef.ok nChar k) && wwfFrom nChar (k + 1) rest

theorem wwfFrom_get {nChar : Nat} : ∀ {k : Nat} {l : List (String × List WRef)},
    wwfFrom nChar k l = true → ∀ (i : Nat) (hi : i < l.length),
      ∀ r ∈ l[i].2, WRef.ok nChar (k + i) r = true
  | _, [], _, _, hi => absurd hi (Nat.not_lt_zero _)
  | k, w :: rest, h, 0, _ => by
    intro r hr
    exact List.all_eq_true.1 (Bool.and_eq_true_iff.1 h).1 r hr
  | k, w :: rest, h, i + 1, hi => by
    intro r hr
    have := wwfFrom_get (Bool.and_eq_true_iff.1 h).2 i (Nat.lt_of_succ_lt_succ hi) r hr
    have e : k + 1 + i = k + (i + 1) := by omega
    rw [← e]
    exact this

/-! ### Resolution -/

/-- **Flatten an item to primitive paths.** Total, because a well-formed
list has no circular references. -/
def flatten {nPrim : Nat} (items : List Item) (h : wfFrom nPrim 0 items = true) :
    (i : Nat) → i < items.length → List Stroke
  | i, hi =>
    (items[i]).attach.flatMap fun r =>
      match r with
      | ⟨.prim p x y, _⟩ => [(⟨p, x, y⟩ : Stroke)]
      | ⟨.item j x y, hr⟩ =>
        have hj : j < i := by
          have := wfFrom_get h i hi _ hr
          simpa [Ref.ok] using this
        (flatten items h j (Nat.lt_trans hj hi)).map fun (s : Stroke) => (⟨s.prim, s.x + x, s.y + y⟩ : Stroke)
termination_by i => i

/-- **Expand a word to its characters**, in order. -/
def expandWord {nChar : Nat} (words : List (String × List WRef))
    (h : wwfFrom nChar 0 words = true) :
    (i : Nat) → i < words.length → List Nat
  | i, hi =>
    (words[i].2).attach.flatMap fun r =>
      match r with
      | ⟨.char c, _⟩ => [c]
      | ⟨.word w, hr⟩ =>
        have hw : w < i := by
          have := wwfFrom_get h i hi _ hr
          simpa [WRef.ok] using this
        expandWord words h w (Nat.lt_trans hw hi)
termination_by i => i

/-- Every primitive in a flattened item exists. -/
theorem flatten_prim_lt {nPrim : Nat} (items : List Item)
    (h : wfFrom nPrim 0 items = true) :
    ∀ (i : Nat) (hi : i < items.length), ∀ s ∈ flatten items h i hi, s.prim < nPrim := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro hi s hs
    rw [flatten] at hs
    obtain ⟨⟨r, hr⟩, _, hs⟩ := List.mem_flatMap.1 hs
    cases r with
    | prim p x y =>
      have hok := wfFrom_get h i hi _ hr
      have hp : p < nPrim := by simpa [Ref.ok] using hok
      have : s = ⟨p, x, y⟩ := by simpa using hs
      rw [this]
      exact hp
    | item j x y =>
      have hok := wfFrom_get h i hi _ hr
      have hj : j < i := by simpa [Ref.ok] using hok
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
      exact ih j hj (Nat.lt_trans hj hi) t ht

/-- Every character index in an expanded word exists. -/
theorem expandWord_lt {nChar : Nat} (words : List (String × List WRef))
    (h : wwfFrom nChar 0 words = true) :
    ∀ (i : Nat) (hi : i < words.length), ∀ c ∈ expandWord words h i hi, c < nChar := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro hi c hc
    rw [expandWord] at hc
    obtain ⟨⟨r, hr⟩, _, hc⟩ := List.mem_flatMap.1 hc
    cases r with
    | char d =>
      have hok := wwfFrom_get h i hi _ hr
      have hd : d < nChar := by simpa [WRef.ok] using hok
      have : c = d := by simpa using hc
      rw [this]
      exact hd
    | word w =>
      have hok := wwfFrom_get h i hi _ hr
      have hw : w < i := by simpa [WRef.ok] using hok
      exact ih w hw (Nat.lt_trans hw hi) c hc

end Bliss
