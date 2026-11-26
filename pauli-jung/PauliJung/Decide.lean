import PauliJung.Core

/-!
# Deciding causal links in finite worlds

A verified checker. For a finite list of states and a Boolean edge function
it computes the causal past of each event by iterated expansion, then
*checks* that the result is closed under direct causes. When the check
passes, the computed set is provably the exact causal past, and whether two
events are causally linked is read off from whether their pasts overlap.

The closure check is then shown to pass always (`certB_true`), so the
procedure is unconditional, and together with a search for a meaning-giving
archetype it decides synchronicity itself (`sync_iff_syncB`).
-/

namespace PauliJung

section Finite

theorem length_filter_le_of_imp {α : Type} {p q : α → Bool}
    (hpq : ∀ a, p a = true → q a = true) :
    ∀ l : List α, (l.filter p).length ≤ (l.filter q).length
  | [] => Nat.le_refl _
  | x :: xs => by
    have ih := length_filter_le_of_imp hpq xs
    cases hp : p x <;> cases hq : q x <;> simp [List.filter, hp, hq] <;>
      first | omega | (have := hpq x hp; simp [hq] at this)

theorem length_filter_lt_of_imp {α : Type} {p q : α → Bool}
    (hpq : ∀ a, p a = true → q a = true) :
    ∀ (l : List α) (a : α), a ∈ l → q a = true → p a = false →
      (l.filter p).length < (l.filter q).length
  | x :: xs, a, ha, hqa, hpa => by
    have le := length_filter_le_of_imp hpq xs
    rcases List.mem_cons.1 ha with rfl | ha
    · simp [List.filter, hqa, hpa]; omega
    · have ih := length_filter_lt_of_imp hpq xs a ha hqa hpa
      cases hp : p x <;> cases hq : q x <;> simp [List.filter, hp, hq] <;>
        first | omega | (have := hpq x hp; simp [hq] at this)


variable {α : Type} [DecidableEq α] (nodes : List α) (edge : α → α → Bool)

/-- Direct causes of members of `S` that are not yet in `S`. -/
def fresh (S : List α) : List α :=
  nodes.filter (fun a => !S.contains a && S.any (fun b => edge a b))

/-- Add all fresh direct causes. -/
def expand (S : List α) : List α := S ++ fresh nodes edge S

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

/-! ### The closure check always passes

Each round either adds a state that was missing or adds nothing; in the
second case the set is already closed. Since at most `nodes.length` states
can be missing, `nodes.length` rounds suffice. -/

theorem closed_of_fresh_nil (hall : ∀ a, a ∈ nodes) (S : List α)
    (h : fresh nodes edge S = []) :
    AncestorClosed (fun a b => edge a b = true) (fun a => a ∈ S) := by
  intro a b hab hb
  by_cases ha : a ∈ S
  · exact ha
  · exfalso
    have hmem : a ∈ fresh nodes edge S :=
      List.mem_filter.2 ⟨hall a, by simpa [ha] using ⟨b, hb, hab⟩⟩
    rw [h] at hmem
    cases hmem

theorem ancN_of_fresh_nil (S : List α) (h : fresh nodes edge S = []) :
    ∀ k, ancN nodes edge k S = S
  | 0 => rfl
  | k + 1 => by
    show ancN nodes edge k (S ++ fresh nodes edge S) = S
    rw [h, List.append_nil]
    exact ancN_of_fresh_nil S h k

/-- States not yet collected. -/
def missing (S : List α) : List α := nodes.filter (fun a => !S.contains a)

theorem missing_lt (S : List α) (a : α) (ha : a ∈ fresh nodes edge S) :
    (missing nodes (expand nodes edge S)).length < (missing nodes S).length := by
  have ha' := List.mem_filter.1 ha
  have haS : a ∉ S := by
    have := (Bool.and_eq_true_iff.1 ha'.2).1
    simpa using this
  apply length_filter_lt_of_imp _ nodes a ha'.1
  · simpa using haS
  · simp [expand, ha]
  · intro c hc
    simp [expand] at hc ⊢
    exact hc.1

theorem ancN_closed (hall : ∀ a, a ∈ nodes) : ∀ (k : Nat) (S : List α),
    (missing nodes S).length ≤ k →
    AncestorClosed (fun a b => edge a b = true) (fun a => a ∈ ancN nodes edge k S)
  | 0, S, h => by
    intro a _ _ _
    have hnil : missing nodes S = [] := List.length_eq_zero_iff.1 (Nat.le_zero.1 h)
    by_cases ha : a ∈ S
    · exact ha
    · exfalso
      have hmem : a ∈ missing nodes S := List.mem_filter.2 ⟨hall a, by simpa using ha⟩
      rw [hnil] at hmem
      cases hmem
  | k + 1, S, h => by
    cases hf : fresh nodes edge S with
    | nil =>
      rw [ancN_of_fresh_nil nodes edge S hf]
      exact closed_of_fresh_nil nodes edge hall S hf
    | cons a as =>
      have hlt := missing_lt nodes edge S a (by rw [hf]; simp)
      exact ancN_closed hall k _ (by omega)

/-- **The computed past is closed**, unconditionally. -/
theorem anc_closed (hall : ∀ a, a ∈ nodes) (x : α) :
    AncestorClosed (fun a b => edge a b = true) (fun a => a ∈ anc nodes edge x) :=
  ancN_closed nodes edge hall _ [x] (List.length_filter_le _ _)

/-- **The computed past is exactly the causal past.** -/
theorem mem_anc_iff (hall : ∀ a, a ∈ nodes) (x a : α) :
    a ∈ anc nodes edge x ↔ a = x ∨ Path (fun a b => edge a b = true) a x := by
  constructor
  · exact anc_sound nodes edge x a
  · rintro (h | h)
    · exact h ▸ self_mem_anc nodes edge x
    · exact h.ancestor (anc_closed nodes edge hall x) (self_mem_anc nodes edge x)

theorem closedB_of_closed (S : List α)
    (h : AncestorClosed (fun a b => edge a b = true) (fun a => a ∈ S)) :
    closedB nodes edge S = true := by
  apply List.all_eq_true.2
  intro a _
  apply List.all_eq_true.2
  intro b _
  cases hab : edge a b
  · simp
  · by_cases hb : b ∈ S
    · simp [hb, h a b hab hb]
    · simp [hb]

/-- **The certificate is always valid.** -/
theorem certB_true (hall : ∀ a, a ∈ nodes) (x y : α) : certB nodes edge x y = true :=
  Bool.and_eq_true_iff.2
    ⟨closedB_of_closed nodes edge _ (anc_closed nodes edge hall x),
     closedB_of_closed nodes edge _ (anc_closed nodes edge hall y)⟩

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

/-! ### Unconditional versions and a full decision procedure -/

/-- **Causal links are decided by computation**, with no side condition. -/
theorem Presentation.linked_iff' (m : W.M) (p : W.P) :
    CausallyLinked W (.inl m) (.inr p) ↔
      linkedB F.nodes F.edge (.inl m) (.inr p) = true :=
  F.linked_iff m p (certB_true F.nodes F.edge F.complete _ _)

/-- Causal links between mind and matter are decidable in a presented world. -/
def Presentation.decLinked (m : W.M) (p : W.P) :
    Decidable (CausallyLinked W (.inl m) (.inr p)) :=
  decidable_of_iff _ (F.linked_iff' m p).symm

end PauliJung

namespace PauliJung

/-- A finite presentation of a whole world: causal structure, neutral
states and archetypes. -/
structure FullPresentation (W : Model) extends Presentation W where
  /-- Every neutral state, listed. -/
  neutrals : List W.U
  /-- Every archetype, listed. -/
  archetypes : List W.A
  neutrals_complete : ∀ u, u ∈ neutrals
  archetypes_complete : ∀ a, a ∈ archetypes

variable {W : Model} [DecidableEq W.M] [DecidableEq W.P]
  [∀ a u, Decidable (W.constellated a u)]
  [∀ a m, Decidable (W.expressesM a m)] [∀ a p, Decidable (W.expressesP a p)]
  (F : FullPresentation W)

/-- Is the pair a meaningful coincidence? Computed by search. -/
def FullPresentation.meaningfulB (m : W.M) (p : W.P) : Bool :=
  F.archetypes.any fun a => F.neutrals.any fun u =>
    decide (W.constellated a u ∧ W.ψ u = m ∧ W.φ u = p ∧
      W.expressesM a m ∧ W.expressesP a p)

theorem FullPresentation.meaningful_iff (m : W.M) (p : W.P) :
    MeaningfulCoincidence W m p ↔ F.meaningfulB m p = true := by
  constructor
  · intro ⟨a, u, h⟩
    exact List.any_eq_true.2 ⟨a, F.archetypes_complete a,
      List.any_eq_true.2 ⟨u, F.neutrals_complete u, decide_eq_true h⟩⟩
  · intro h
    obtain ⟨a, _, ha⟩ := List.any_eq_true.1 h
    obtain ⟨u, _, hu⟩ := List.any_eq_true.1 ha
    exact ⟨a, u, of_decide_eq_true hu⟩

/-- Is the pair a synchronicity? Computed. -/
def FullPresentation.syncB (m : W.M) (p : W.P) : Bool :=
  F.meaningfulB m p && !linkedB F.nodes F.edge (.inl m) (.inr p)

/-- **Synchronicity is decidable in finite worlds**: the computed verdict is
correct in both directions. -/
theorem FullPresentation.sync_iff_syncB (m : W.M) (p : W.P) :
    Synchronicity W m p ↔ F.syncB m p = true := by
  unfold Synchronicity FullPresentation.syncB
  rw [F.meaningful_iff, F.toPresentation.linked_iff']
  simp

/-- The decision procedure as a `Decidable` instance. -/
def FullPresentation.decSync (m : W.M) (p : W.P) : Decidable (Synchronicity W m p) :=
  decidable_of_iff _ (F.sync_iff_syncB m p).symm

end PauliJung
