import PauliJung.Core

/-!
# Deciding causal links in finite worlds

A verified checker. For a finite list of states and a Boolean edge function
it computes the causal past of each event by iterated expansion, then
*checks* that the result is closed under direct causes. When the check
passes, the computed set is provably the exact causal past, and whether two
events are causally linked is read off from whether their pasts overlap.

The closure check is part of the certificate, so no bound on path lengths
has to be proved; the theorems below are sound and complete whenever the
check succeeds (and with `nodes.length` rounds it always does in practice).
-/

namespace PauliJung

section Finite

variable {α : Type} [DecidableEq α] (nodes : List α) (edge : α → α → Bool)

/-- Add all direct causes of members of `S` that are not yet in `S`. -/
def expand (S : List α) : List α :=
  S ++ nodes.filter (fun a => !S.contains a && S.any (fun b => edge a b))

/-- `k` rounds of expansion. -/
def ancN : Nat → List α → List α
  | 0, S => S
  | k + 1, S => ancN k (expand nodes edge S)

/-- The computed causal past of `x` (including `x`). -/
def anc (x : α) : List α := ancN nodes edge nodes.length [x]

/-- Is `S` closed under direct causes? -/
def closedB (S : List α) : Bool :=
  nodes.all fun a => nodes.all fun b => !(edge a b && S.contains b) || S.contains a

/-- Do the computed pasts of `x` and `y` overlap? -/
def linkedB (x y : α) : Bool :=
  (anc nodes edge x).any fun a => (anc nodes edge y).contains a

/-- Did both closure checks pass? -/
def certB (x y : α) : Bool :=
  closedB nodes edge (anc nodes edge x) && closedB nodes edge (anc nodes edge y)

theorem expand_sound (x : α) (S : List α)
    (h : ∀ a ∈ S, a = x ∨ Path (fun a b => edge a b = true) a x) :
    ∀ a ∈ expand nodes edge S, a = x ∨ Path (fun a b => edge a b = true) a x := by
  intro a ha
  rcases List.mem_append.1 ha with h1 | h1
  · exact h a h1
  · obtain ⟨b, hb, hab⟩ := List.any_eq_true.1 (Bool.and_eq_true_iff.1 (List.mem_filter.1 h1).2).2
    rcases h b hb with hbx | hbx
    · exact Or.inr (Path.single (hbx ▸ hab))
    · exact Or.inr (Path.head hab hbx)

theorem ancN_sound (x : α) : ∀ (k : Nat) (S : List α),
    (∀ a ∈ S, a = x ∨ Path (fun a b => edge a b = true) a x) →
    ∀ a ∈ ancN nodes edge k S, a = x ∨ Path (fun a b => edge a b = true) a x
  | 0, _, h => h
  | k + 1, S, h => ancN_sound x k _ (expand_sound nodes edge x S h)

theorem mem_ancN : ∀ (k : Nat) (S : List α) (a : α), a ∈ S → a ∈ ancN nodes edge k S
  | 0, _, _, h => h
  | k + 1, _, a, h => mem_ancN k _ a (List.mem_append.2 (Or.inl h))

/-- Everything computed really is in the causal past. -/
theorem anc_sound (x a : α) (h : a ∈ anc nodes edge x) :
    a = x ∨ Path (fun a b => edge a b = true) a x :=
  ancN_sound nodes edge x _ [x] (fun a ha => Or.inl (by simpa using ha)) a h

theorem self_mem_anc (x : α) : x ∈ anc nodes edge x :=
  mem_ancN nodes edge _ [x] x (by simp)

theorem closedB_closed (hall : ∀ a, a ∈ nodes) (S : List α)
    (h : closedB nodes edge S = true) :
    AncestorClosed (fun a b => edge a b = true) (fun a => a ∈ S) := by
  intro a b hab hb
  have h1 := List.all_eq_true.1 h a (hall a)
  have h2 := List.all_eq_true.1 h1 b (hall b)
  simpa [hab, hb] using h2

/-- With a passed closure check, the computed past is complete. -/
theorem anc_complete (hall : ∀ a, a ∈ nodes) (x a : α)
    (hx : closedB nodes edge (anc nodes edge x) = true)
    (h : a = x ∨ Path (fun a b => edge a b = true) a x) : a ∈ anc nodes edge x := by
  rcases h with h | h
  · exact h ▸ self_mem_anc nodes edge x
  · exact h.ancestor (closedB_closed nodes edge hall _ hx) (self_mem_anc nodes edge x)

/-- **Correctness of the checker** on the raw relation. -/
theorem linkedB_iff (hall : ∀ a, a ∈ nodes) {x y : α} (hne : x ≠ y)
    (hc : certB nodes edge x y = true) :
    (Path (fun a b => edge a b = true) x y ∨ Path (fun a b => edge a b = true) y x ∨
        ∃ z, Path (fun a b => edge a b = true) z x ∧ Path (fun a b => edge a b = true) z y) ↔
      linkedB nodes edge x y = true := by
  have hc' := Bool.and_eq_true_iff.1 hc
  have cx := anc_complete nodes edge hall x
  have cy := anc_complete nodes edge hall y
  constructor
  · intro h
    apply List.any_eq_true.2
    rcases h with h | h | ⟨z, hzx, hzy⟩
    · exact ⟨x, cx x hc'.1 (Or.inl rfl), by simpa using cy x hc'.2 (Or.inr h)⟩
    · exact ⟨y, cx y hc'.1 (Or.inr h), by simpa using cy y hc'.2 (Or.inl rfl)⟩
    · exact ⟨z, cx z hc'.1 (Or.inr hzx), by simpa using cy z hc'.2 (Or.inr hzy)⟩
  · intro h
    obtain ⟨a, hax, hay⟩ := List.any_eq_true.1 h
    have hay' : a ∈ anc nodes edge y := by simpa using hay
    rcases anc_sound nodes edge x a hax with h1 | h1 <;>
      rcases anc_sound nodes edge y a hay' with h2 | h2
    · exact absurd (h1.symm.trans h2) hne
    · exact Or.inl (h1 ▸ h2)
    · exact Or.inr (Or.inl (h2 ▸ h1))
    · exact Or.inr (Or.inr ⟨a, h1, h2⟩)

end Finite

/-- A finite presentation of a world's causal structure. -/
structure Presentation (W : Model) where
  /-- Every manifest state, listed. -/
  nodes : List (Sum W.M W.P)
  /-- Direct causation as a Boolean function. -/
  edge : Sum W.M W.P → Sum W.M W.P → Bool
  complete : ∀ x, x ∈ nodes
  faithful : ∀ x y, W.causes x y ↔ edge x y = true

variable {W : Model} [DecidableEq (Sum W.M W.P)] (F : Presentation W)

/-- **The checker decides causal links.** -/
theorem Presentation.linked_iff (m : W.M) (p : W.P)
    (hc : certB F.nodes F.edge (.inl m) (.inr p) = true) :
    CausallyLinked W (.inl m) (.inr p) ↔
      linkedB F.nodes F.edge (.inl m) (.inr p) = true := by
  have to : ∀ {a b}, Path W.causes a b → Path (fun a b => F.edge a b = true) a b :=
    fun h => Path.mono (fun a b => (F.faithful a b).1) h
  have from' : ∀ {a b}, Path (fun a b => F.edge a b = true) a b → Path W.causes a b :=
    fun h => Path.mono (fun a b => (F.faithful a b).2) h
  rw [← linkedB_iff F.nodes F.edge F.complete (inl_ne_inr W m p) hc]
  constructor
  · rintro (h | h | ⟨z, h1, h2⟩)
    · exact Or.inl (to h)
    · exact Or.inr (Or.inl (to h))
    · exact Or.inr (Or.inr ⟨z, to h1, to h2⟩)
  · rintro (h | h | ⟨z, h1, h2⟩)
    · exact Or.inl (from' h)
    · exact Or.inr (Or.inl (from' h))
    · exact Or.inr (Or.inr ⟨z, from' h1, from' h2⟩)

/-- Verdict "acausal", by computation. -/
theorem Presentation.unlinked (m : W.M) (p : W.P)
    (h : (certB F.nodes F.edge (.inl m) (.inr p) &&
          !linkedB F.nodes F.edge (.inl m) (.inr p)) = true) :
    ¬ CausallyLinked W (.inl m) (.inr p) := by
  have h' := Bool.and_eq_true_iff.1 h
  intro hl
  have := (F.linked_iff m p h'.1).1 hl
  simp [this] at h'

/-- Verdict "causal", by computation. -/
theorem Presentation.linked (m : W.M) (p : W.P)
    (h : (certB F.nodes F.edge (.inl m) (.inr p) &&
          linkedB F.nodes F.edge (.inl m) (.inr p)) = true) :
    CausallyLinked W (.inl m) (.inr p) :=
  have h' := Bool.and_eq_true_iff.1 h
  (F.linked_iff m p h'.1).2 h'.2

/-- A meaningful coincidence is a synchronicity exactly when the checker
finds no link. -/
theorem Presentation.sync_iff (m : W.M) (p : W.P)
    (hc : certB F.nodes F.edge (.inl m) (.inr p) = true) :
    Synchronicity W m p ↔
      MeaningfulCoincidence W m p ∧ linkedB F.nodes F.edge (.inl m) (.inr p) = false := by
  unfold Synchronicity
  rw [F.linked_iff m p hc]
  simp

end PauliJung
