import PauliJung.Core

/-!
# Relatives of the conjecture: positions on mind and matter

Classical positions stated as properties of a dual-aspect world, and what
each implies for synchronicity. The Pauli–Jung picture differs from
parallelism in *allowing* mind–matter causation and in making acausal
correlations sporadic rather than universal.
-/

namespace PauliJung

variable (W : Model)

/-- Is a manifest state mental? -/
def isMental {α β : Type} : Sum α β → Bool
  | .inl _ => true
  | .inr _ => false

/-- **Parallelism** (Leibniz, Spinoza): causation never crosses between the
mental and the physical. -/
def Parallelist : Prop := ∀ x y, W.causes x y → isMental x = isMental y

/-- **Epiphenomenalism**: nothing mental directly causes anything physical. -/
def Epiphenomenal : Prop := ∀ m p, ¬ W.causes (.inl m) (.inr p)

/-- **Interactionism**: causation crosses in both directions. -/
def Interactionist : Prop :=
  (∃ m p, W.causes (.inl m) (.inr p)) ∧ ∃ p m, W.causes (.inr p) (.inl m)

/-- Under parallelism no mental state is causally linked to a physical one. -/
theorem parallelist_noLink (h : Parallelist W) (m : W.M) (p : W.P) :
    ¬ CausallyLinked W (.inl m) (.inr p) :=
  noLink_of_separated W isMental h (by simp [isMental])

/-- **Pre-established harmony.** Under parallelism every meaningful
coincidence is a synchronicity: acausal orderedness is the rule, not the
exception. -/
theorem parallelism_all_sync (h : Parallelist W) {m : W.M} {p : W.P}
    (hm : MeaningfulCoincidence W m p) : Synchronicity W m p :=
  ⟨hm, parallelist_noLink W h m p⟩

/-- Parallelism contradicts the manifest Reichenbach principle in any
non-empty world. -/
theorem parallelist_not_reichenbach (h : Parallelist W) (u : W.U) :
    ¬ ManifestReichenbach W :=
  fun hr => parallelist_noLink W h _ _ (hr u)

/-- Parallelism and interactionism exclude each other. -/
theorem parallelist_not_interactionist (h : Parallelist W) : ¬ Interactionist W := by
  intro ⟨⟨m, p, hmp⟩, _⟩
  have := h _ _ hmp
  cases this

/-- Under epiphenomenalism the mind steers nothing physical, not even
indirectly. -/
theorem epiphenomenal_no_control (h : Epiphenomenal W) (m : W.M) (p : W.P) :
    ¬ Controls W m p := by
  intro hc
  have key : isMental (Sum.inl m : Sum W.M W.P) = true →
      isMental (Sum.inr p : Sum W.M W.P) = true :=
    Path.invariant (I := fun a => isMental a = true)
      (fun a b hab ha => by
        cases a with
        | inr _ => cases ha
        | inl a =>
          cases b with
          | inl _ => rfl
          | inr b => exact absurd hab (h a b)) hc
  cases key rfl

/-- Parallelism is a special case of epiphenomenalism. -/
theorem parallelist_epiphenomenal (h : Parallelist W) : Epiphenomenal W := by
  intro m p hmp
  have := h _ _ hmp
  cases this

/-! ### Complementarity

Pauli's reading of the mind–matter relation: the two aspects are not two
views that could be merged into one, but mutually unconstrained descriptions
of the same ground. -/

/-- The aspects are **complementary**: any mental aspect that occurs can be
combined with any physical aspect that occurs. -/
def Complementary : Prop :=
  ∀ u v : W.U, ∃ w : W.U, W.ψ w = W.ψ u ∧ W.φ w = W.φ v

/-- Complementary aspects with more than one physical value: no idealist
reduction. -/
theorem complementary_not_idealist (h : Complementary W) {u v : W.U}
    (hne : W.φ u ≠ W.φ v) : ¬ PhysicalReducesToMental W := by
  intro ⟨f, hf⟩
  obtain ⟨w, hψ, hφ⟩ := h u v
  apply hne
  rw [hf u, ← hψ, ← hf w, hφ]

/-- Complementary aspects with more than one mental value: no physicalist
reduction. -/
theorem complementary_not_physicalist (h : Complementary W) {u v : W.U}
    (hne : W.ψ u ≠ W.ψ v) : ¬ MentalReducesToPhysical W := by
  intro ⟨g, hg⟩
  obtain ⟨w, hψ, hφ⟩ := h u v
  apply hne
  rw [← hψ, hg w, hφ, ← hg v]

/-- **Complementarity implies non-reductive monism.** -/
theorem complementary_nonreductive (h : Complementary W) {u v u' v' : W.U}
    (hφ : W.φ u ≠ W.φ v) (hψ : W.ψ u' ≠ W.ψ v') :
    ¬ PhysicalReducesToMental W ∧ ¬ MentalReducesToPhysical W :=
  ⟨complementary_not_idealist W h hφ, complementary_not_physicalist W h hψ⟩

end PauliJung
