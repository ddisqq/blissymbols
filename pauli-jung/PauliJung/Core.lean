/-!
# Core: causal paths, dual-aspect models, synchronicity

1. Causal paths and causal separation
2. Dual-aspect models
3. Synchronicity and its basic properties (incl. no-signalling)
4. Synchronicity versus Reichenbach's common-cause principle
5. Non-reductive monism
6. Sporadic synchronicity versus lawlike acausal orderedness
-/

namespace PauliJung

/-! ## 1. Causal paths and causal separation -/

/-- Transitive closure of a relation (defined here to stay Mathlib-free). -/
inductive Path {α : Type} (r : α → α → Prop) : α → α → Prop
  | single {a b : α} : r a b → Path r a b
  | tail {a b c : α} : Path r a b → r b c → Path r a c

/-- If no step is possible, no path exists. -/
theorem Path.of_empty {α : Type} {r : α → α → Prop}
    (h : ∀ a b, ¬ r a b) {a b : α} : ¬ Path r a b := by
  intro p
  induction p with
  | single hab => exact h _ _ hab
  | tail _ hbc _ => exact h _ _ hbc

/-- Paths never leave a causally sealed component: any labelling preserved by
single steps is preserved by whole paths. -/
theorem Path.preserves {α β : Type} {r : α → α → Prop} (side : α → β)
    (h : ∀ a b, r a b → side a = side b) {a b : α} (p : Path r a b) :
    side a = side b := by
  induction p with
  | single hab => exact h _ _ hab
  | tail _ hbc ih => exact ih.trans (h _ _ hbc)

/-- Prepend a step to a path. -/
theorem Path.head {α : Type} {r : α → α → Prop} {a b c : α}
    (hab : r a b) (p : Path r b c) : Path r a c := by
  induction p with
  | single hbc => exact Path.tail (Path.single hab) hbc
  | tail _ hcd ih => exact Path.tail ih hcd

/-- Paths compose. -/
theorem Path.trans {α : Type} {r : α → α → Prop} {a b c : α}
    (p : Path r a b) (q : Path r b c) : Path r a c := by
  induction q with
  | single hbc => exact Path.tail p hbc
  | tail _ hcd ih => exact Path.tail ih hcd

/-- Enlarging the relation keeps every path. -/
theorem Path.mono {α : Type} {r s : α → α → Prop}
    (h : ∀ a b, r a b → s a b) {a b : α} (p : Path r a b) : Path s a b := by
  induction p with
  | single hab => exact Path.single (h _ _ hab)
  | tail _ hbc ih => exact Path.tail ih (h _ _ hbc)

/-- Any property carried forward by single steps is carried by whole paths. -/
theorem Path.invariant {α : Type} {r : α → α → Prop} {I : α → Prop}
    (h : ∀ a b, r a b → I a → I b) {a b : α} (p : Path r a b) : I a → I b := by
  induction p with
  | single hab => exact h _ _ hab
  | tail _ hbc ih => exact fun ha => h _ _ hbc (ih ha)

/-- A quantity that never decreases along a step never decreases along a path. -/
theorem Path.le {α : Type} {r : α → α → Prop} (f : α → Nat)
    (h : ∀ a b, r a b → f a ≤ f b) {a b : α} (p : Path r a b) : f a ≤ f b := by
  induction p with
  | single hab => exact h _ _ hab
  | tail _ hbc ih => exact Nat.le_trans ih (h _ _ hbc)

/-- A set is ancestor-closed if it contains every direct cause of its members. -/
def AncestorClosed {α : Type} (r : α → α → Prop) (S : α → Prop) : Prop :=
  ∀ a b, r a b → S b → S a

/-- An ancestor-closed set contains every indirect cause of its members. -/
theorem Path.ancestor {α : Type} {r : α → α → Prop} {S : α → Prop}
    (hS : AncestorClosed r S) {a b : α} (p : Path r a b) : S b → S a := by
  induction p with
  | single hab => exact hS _ _ hab
  | tail _ hbc ih => exact fun hc => ih (hS _ _ hbc hc)

/-! ## 2. Dual-aspect models -/

/-- A dual-aspect world. -/
structure Model where
  /-- Psychophysically neutral reality (the *unus mundus*). -/
  U : Type
  /-- Mental states. -/
  M : Type
  /-- Physical states. -/
  P : Type
  /-- Archetypes. -/
  A : Type
  /-- Mental aspect of a neutral state. -/
  ψ : U → M
  /-- Physical aspect of a neutral state. -/
  φ : U → P
  /-- Direct causation among manifest states (mental or physical). -/
  causes : Sum M P → Sum M P → Prop
  /-- Archetype `a` is constellated in neutral state `u`. -/
  constellated : A → U → Prop
  /-- Archetype `a` gives meaning to a mental state. -/
  expressesM : A → M → Prop
  /-- Archetype `a` gives meaning to a physical state. -/
  expressesP : A → P → Prop

variable (W : Model)

/-! ## 3. Synchronicity -/

/-- Two manifest states are causally linked if one causes the other (possibly
indirectly) or they share a common cause: Reichenbach's menu of causal
explanations. -/
def CausallyLinked (x y : Sum W.M W.P) : Prop :=
  Path W.causes x y ∨ Path W.causes y x ∨
    ∃ z, Path W.causes z x ∧ Path W.causes z y

/-- In a world without causation nothing is causally linked. -/
theorem noLink_of_noCause (hW : ∀ x y, ¬ W.causes x y)
    (x y : Sum W.M W.P) : ¬ CausallyLinked W x y := by
  intro h
  rcases h with h | h | ⟨_, h, _⟩ <;> exact Path.of_empty hW h

/-- **Causal separation.** States in different sealed components are not
causally linked, not even through a common cause. Causation *within* each
component, including mind–matter causation such as perception, is allowed. -/
theorem noLink_of_separated {β : Type} (side : Sum W.M W.P → β)
    (hW : ∀ x y, W.causes x y → side x = side y)
    {x y : Sum W.M W.P} (hxy : side x ≠ side y) : ¬ CausallyLinked W x y := by
  intro h
  rcases h with h | h | ⟨_, hzx, hzy⟩
  · exact hxy (Path.preserves side hW h)
  · exact hxy (Path.preserves side hW h).symm
  · exact hxy ((Path.preserves side hW hzx).symm.trans (Path.preserves side hW hzy))

/-- A **meaningful coincidence**: `m` and `p` are the two aspects of one neutral
state in which an archetype is constellated, and that archetype gives meaning
to both. Nothing is said yet about causation. -/
def MeaningfulCoincidence (m : W.M) (p : W.P) : Prop :=
  ∃ (a : W.A) (u : W.U),
    W.constellated a u ∧ W.ψ u = m ∧ W.φ u = p ∧
    W.expressesM a m ∧ W.expressesP a p

/-- A synchronistic event: mental state `m` and physical state `p` are the two
aspects of one neutral state in which an archetype is constellated, that
archetype gives meaning to both, and no causal link joins them. -/
def Synchronicity (m : W.M) (p : W.P) : Prop :=
  MeaningfulCoincidence W m p ∧ ¬ CausallyLinked W (.inl m) (.inr p)

/-- Synchronicity is exactly a meaningful coincidence that is not causal. -/
theorem sync_iff {m : W.M} {p : W.P} :
    Synchronicity W m p ↔
      MeaningfulCoincidence W m p ∧ ¬ CausallyLinked W (.inl m) (.inr p) :=
  Iff.rfl

/-- A meaningful coincidence with a causal link is ordinary, not synchronistic. -/
theorem not_sync_of_linked {m : W.M} {p : W.P}
    (h : CausallyLinked W (.inl m) (.inr p)) : ¬ Synchronicity W m p :=
  fun hs => hs.2 h

/-- How to certify a synchronicity: a constellated archetype, meaning on both
sides, and causal separation of the two aspects. -/
theorem sync_of_separated {β : Type} (side : Sum W.M W.P → β)
    (hsep : ∀ x y, W.causes x y → side x = side y)
    (a : W.A) (u : W.U) (hc : W.constellated a u)
    (hm : W.expressesM a (W.ψ u)) (hp : W.expressesP a (W.φ u))
    (hxy : side (.inl (W.ψ u)) ≠ side (.inr (W.φ u))) :
    Synchronicity W (W.ψ u) (W.φ u) :=
  ⟨⟨a, u, hc, rfl, rfl, hm, hp⟩, noLink_of_separated W side hsep hxy⟩

/-! ### Complete certificates of acausality

Separation into sealed components is sound but not complete: two events may
share a common *effect* (a collider, e.g. an observer who registers both)
without being causally linked. The exact criterion is that their causal
pasts are disjoint. -/

/-- **Disjoint causal pasts.** If `x` and `y` lie in disjoint ancestor-closed
sets, they are not causally linked. Common effects are allowed. -/
theorem noLink_of_ancestral (S T : Sum W.M W.P → Prop)
    (hS : AncestorClosed W.causes S) (hT : AncestorClosed W.causes T)
    (hdis : ∀ a, S a → T a → False)
    {x y : Sum W.M W.P} (hx : S x) (hy : T y) : ¬ CausallyLinked W x y := by
  intro h
  rcases h with h | h | ⟨z, hzx, hzy⟩
  · exact hdis x hx (h.ancestor hT hy)
  · exact hdis y (h.ancestor hS hx) hy
  · exact hdis z (hzx.ancestor hS hx) (hzy.ancestor hT hy)

/-- **Completeness.** For distinct events, absence of a causal link is
*equivalent* to the existence of disjoint ancestor-closed sets around them. -/
theorem noLink_iff_ancestral {x y : Sum W.M W.P} (hne : x ≠ y) :
    ¬ CausallyLinked W x y ↔
      ∃ S T : Sum W.M W.P → Prop,
        AncestorClosed W.causes S ∧ AncestorClosed W.causes T ∧
        (∀ a, S a → T a → False) ∧ S x ∧ T y := by
  constructor
  · intro h
    refine ⟨fun a => a = x ∨ Path W.causes a x, fun a => a = y ∨ Path W.causes a y,
      ?_, ?_, ?_, Or.inl rfl, Or.inl rfl⟩
    · intro a b hab hb
      rcases hb with hb | hb
      · exact Or.inr (Path.single (hb ▸ hab))
      · exact Or.inr (Path.head hab hb)
    · intro a b hab hb
      rcases hb with hb | hb
      · exact Or.inr (Path.single (hb ▸ hab))
      · exact Or.inr (Path.head hab hb)
    · intro a ha hb
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact hne (ha.symm.trans hb)
      · exact h (Or.inl (ha ▸ hb))
      · exact h (Or.inr (Or.inl (hb ▸ ha)))
      · exact h (Or.inr (Or.inr ⟨a, ha, hb⟩))
  · intro ⟨S, T, hS, hT, hdis, hx, hy⟩
    exact noLink_of_ancestral W S T hS hT hdis hx hy

/-- A mental and a physical state are never the same manifest state. -/
theorem inl_ne_inr (m : W.M) (p : W.P) :
    (Sum.inl m : Sum W.M W.P) ≠ Sum.inr p := fun h => nomatch h

/-- Certify a synchronicity by disjoint causal pasts, given as Boolean
labellings so that finite cases can be checked by enumeration. -/
theorem sync_of_ancestral (sS sT : Sum W.M W.P → Bool)
    (hS : ∀ a b, W.causes a b → sS b = true → sS a = true)
    (hT : ∀ a b, W.causes a b → sT b = true → sT a = true)
    (hdis : ∀ a, sS a = true → sT a = true → False)
    (a : W.A) (u : W.U) (hc : W.constellated a u)
    (hm : W.expressesM a (W.ψ u)) (hp : W.expressesP a (W.φ u))
    (hx : sS (.inl (W.ψ u)) = true) (hy : sT (.inr (W.φ u)) = true) :
    Synchronicity W (W.ψ u) (W.φ u) :=
  ⟨⟨a, u, hc, rfl, rfl, hm, hp⟩,
    noLink_of_ancestral W (fun a => sS a = true) (fun a => sT a = true) hS hT hdis hx hy⟩

/-- **Characterization.** A pair is synchronistic exactly when it is a
meaningful coincidence whose two terms have disjoint causal pasts. -/
theorem sync_iff_ancestral {m : W.M} {p : W.P} :
    Synchronicity W m p ↔
      MeaningfulCoincidence W m p ∧
      ∃ S T : Sum W.M W.P → Prop,
        AncestorClosed W.causes S ∧ AncestorClosed W.causes T ∧
        (∀ a, S a → T a → False) ∧ S (.inl m) ∧ T (.inr p) :=
  ⟨fun h => ⟨h.1, (noLink_iff_ancestral W (inl_ne_inr W m p)).1 h.2⟩,
   fun h => ⟨h.1, (noLink_iff_ancestral W (inl_ne_inr W m p)).2 h.2⟩⟩

/-- A synchronicity is never a causal connection. -/
theorem sync_acausal {m : W.M} {p : W.P} (h : Synchronicity W m p) :
    ¬ CausallyLinked W (.inl m) (.inr p) :=
  h.2

/-- The two terms of a synchronicity share a neutral origin. -/
theorem sync_common_ground {m : W.M} {p : W.P} (h : Synchronicity W m p) :
    ∃ u : W.U, W.ψ u = m ∧ W.φ u = p := by
  obtain ⟨⟨_, u, _, hm, hp, _, _⟩, _⟩ := h
  exact ⟨u, hm, hp⟩

/-- Every synchronicity is carried by a constellated archetype. -/
theorem sync_constellated {m : W.M} {p : W.P} (h : Synchronicity W m p) :
    ∃ (a : W.A) (u : W.U), W.constellated a u := by
  obtain ⟨⟨a, u, hc, _⟩, _⟩ := h
  exact ⟨a, u, hc⟩

/-- `m` can steer `p`: a causal path from mind to matter. -/
def Controls (m : W.M) (p : W.P) : Prop :=
  Path W.causes (.inl m) (.inr p)

/-- **No-signalling.** A synchronicity cannot be used to steer matter by mind... -/
theorem sync_no_signal {m : W.M} {p : W.P} (h : Synchronicity W m p) :
    ¬ Controls W m p :=
  fun hc => h.2 (Or.inl hc)

/-- ...nor mind by matter. -/
theorem sync_no_backsignal {m : W.M} {p : W.P} (h : Synchronicity W m p) :
    ¬ Path W.causes (.inr p) (.inl m) :=
  fun hc => h.2 (Or.inr (Or.inl hc))

/-! ## 4. Synchronicity versus Reichenbach -/

/-- **Manifest Reichenbach principle**: the two aspects of every neutral state
are causally linked on the manifest level. -/
def ManifestReichenbach : Prop :=
  ∀ u : W.U, CausallyLinked W (.inl (W.ψ u)) (.inr (W.φ u))

/-- **Main theorem.** Under the manifest Reichenbach principle, synchronicity is
impossible. The Pauli–Jung conjecture therefore *requires* that some
mind–matter correlations are explained by the neutral level, not by causes. -/
theorem no_sync_under_reichenbach (h : ManifestReichenbach W) :
    ∀ (m : W.M) (p : W.P), ¬ Synchronicity W m p := by
  intro m p ⟨⟨_, u, _, hm, hp, _, _⟩, hac⟩
  subst hm
  subst hp
  exact hac (h u)

/-- Conversely, any synchronicity refutes the manifest Reichenbach principle. -/
theorem sync_refutes_reichenbach {m : W.M} {p : W.P}
    (h : Synchronicity W m p) : ¬ ManifestReichenbach W :=
  fun hr => no_sync_under_reichenbach W hr m p h

/-! ## 5. Non-reductive monism -/

/-- The physical aspect is a function of the mental aspect (idealist reduction). -/
def PhysicalReducesToMental : Prop :=
  ∃ f : W.M → W.P, ∀ u, W.φ u = f (W.ψ u)

/-- The mental aspect is a function of the physical aspect (physicalist reduction). -/
def MentalReducesToPhysical : Prop :=
  ∃ g : W.P → W.M, ∀ u, W.ψ u = g (W.φ u)

/-- If both aspects are locked to each other, each reduces to the other only
when the aspect maps allow it; in general the two reductions are independent
(see `Models`). A reduction never by itself produces a causal link. -/
theorem reduction_adds_no_cause (hW : ∀ x y, ¬ W.causes x y)
    (_ : PhysicalReducesToMental W) (u : W.U) :
    ¬ CausallyLinked W (.inl (W.ψ u)) (.inr (W.φ u)) :=
  noLink_of_noCause W hW _ _

/-! ## 6. Sporadic versus lawlike orderedness

Jung distinguished synchronicity proper, which is sporadic and
irreproducible, from *general acausal orderedness*, which holds always
(his example: the properties of the natural numbers). -/

/-- The archetype orders every neutral state. -/
def Lawlike (a : W.A) : Prop := ∀ u, W.constellated a u

/-- The archetype is constellated somewhere but not everywhere. -/
def Sporadic (a : W.A) : Prop :=
  (∃ u, W.constellated a u) ∧ ∃ u, ¬ W.constellated a u

/-- Sporadic and lawlike exclude each other. -/
theorem sporadic_not_lawlike {a : W.A} (h : Sporadic W a) : ¬ Lawlike W a := by
  intro hl
  obtain ⟨_, u, hu⟩ := h
  exact hu (hl u)

end PauliJung
