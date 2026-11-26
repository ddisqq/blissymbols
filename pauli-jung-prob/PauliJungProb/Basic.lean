import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import PauliJung.Frequency

/-!
# Measure-theoretic companion to the Pauli–Jung formalization

The core package models probability by counting in finite ensembles. Here
the same notions are stated for an arbitrary probability measure, using
Mathlib:

* positive correlation and uncorrelatedness of events;
* **Reichenbach's common-cause theorem**: an event that screens off two
  others and raises the probability of each makes them positively
  correlated;
* locked aspects of a neutral state are positively correlated, with no cause;
* conditional on a single neutral state, any two events are independent;
* a bridge showing that the counting definitions of the core package are
  the frequency instances of the real-valued ones.
-/

open MeasureTheory ProbabilityTheory

namespace PauliJungProb

/-! ### The algebra behind Reichenbach's theorem -/

/-- With `c + d = 1`, strata probabilities `a₁, b₁, x₁` (inside the cause)
and `a₀, b₀, x₀` (outside), screening-off in both strata and a raised
probability of each effect give a positive covariance. The identity behind
it: `(P(AB) − P(A)P(B))·cd = (a₁d − a₀c)(b₁d − b₀c)`. -/
theorem reichenbach_real {c d a₁ a₀ b₁ b₀ x₁ x₀ : ℝ}
    (hc : 0 < c) (hd : 0 < d) (hcd : c + d = 1)
    (h₁ : x₁ * c = a₁ * b₁) (h₀ : x₀ * d = a₀ * b₀)
    (hA : a₀ * c < a₁ * d) (hB : b₀ * c < b₁ * d) :
    (a₁ + a₀) * (b₁ + b₀) < x₁ + x₀ := by
  have key : ((x₁ + x₀) - (a₁ + a₀) * (b₁ + b₀)) * (c * d)
      = (a₁ * d - a₀ * c) * (b₁ * d - b₀ * c) := by
    linear_combination d * h₁ + c * h₀ - (a₁ * b₁ * d + a₀ * b₀ * c) * hcd
  have hpos : 0 < (a₁ * d - a₀ * c) * (b₁ * d - b₀ * c) :=
    mul_pos (sub_pos.2 hA) (sub_pos.2 hB)
  have hcd' : 0 < c * d := mul_pos hc hd
  by_contra hle
  have hle' : (x₁ + x₀) - (a₁ + a₀) * (b₁ + b₀) ≤ 0 := by linarith [not_lt.1 hle]
  have : ((x₁ + x₀) - (a₁ + a₀) * (b₁ + b₀)) * (c * d) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hle' hcd'.le
  linarith

/-! ### Correlation for a probability measure -/

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/-- `A` and `B` are positively correlated: `P(A)P(B) < P(A ∩ B)`. -/
def PosCorr (A B : Set Ω) : Prop := μ.real A * μ.real B < μ.real (A ∩ B)

/-- `A` and `B` are uncorrelated: `P(A ∩ B) = P(A)P(B)`. -/
def Uncorr (A B : Set Ω) : Prop := μ.real (A ∩ B) = μ.real A * μ.real B

variable {μ} {A B C : Set Ω}

theorem PosCorr.symm (h : PosCorr μ A B) : PosCorr μ B A := by
  unfold PosCorr at *
  rwa [Set.inter_comm, mul_comm]

theorem Uncorr.not_posCorr (h : Uncorr μ A B) : ¬ PosCorr μ A B := by
  unfold PosCorr Uncorr at *
  intro hc
  linarith

/-- Mathlib's independence of two events implies uncorrelatedness. -/
theorem uncorr_of_indepSet (h : IndepSet A B μ) : Uncorr μ A B := by
  unfold Uncorr
  simp [Measure.real, h.measure_inter_eq_mul, ENNReal.toReal_mul]

/-- Independent events are not positively correlated. -/
theorem not_posCorr_of_indepSet (h : IndepSet A B μ) : ¬ PosCorr μ A B :=
  (uncorr_of_indepSet h).not_posCorr

/-! ### Reichenbach's common-cause principle -/

variable (μ) in
/-- `C` is a **Reichenbachian common cause** of `A` and `B`: it is neither
impossible nor certain, it screens `A` off from `B` (inside and outside
`C`), and it raises the probability of each. Conditional probabilities are
written multiplied out, so no division by zero can occur. -/
structure CommonCause (C A B : Set Ω) : Prop where
  pos : 0 < μ.real C
  lt_one : μ.real C < 1
  screens : μ.real (A ∩ B ∩ C) * μ.real C = μ.real (A ∩ C) * μ.real (B ∩ C)
  screens_compl :
    μ.real (A ∩ B ∩ Cᶜ) * μ.real Cᶜ = μ.real (A ∩ Cᶜ) * μ.real (B ∩ Cᶜ)
  raisesA : μ.real (A ∩ Cᶜ) * μ.real C < μ.real (A ∩ C) * μ.real Cᶜ
  raisesB : μ.real (B ∩ Cᶜ) * μ.real C < μ.real (B ∩ C) * μ.real Cᶜ

/-- **Reichenbach's theorem.** A common cause makes its effects positively
correlated. This is why a correlation *suggests* a common cause; the
Pauli–Jung conjecture is that for some mind–matter correlations no such
manifest event `C` exists. -/
theorem CommonCause.posCorr [IsProbabilityMeasure μ] (hC : MeasurableSet C)
    (h : CommonCause μ C A B) : PosCorr μ A B := by
  have hsum : μ.real C + μ.real Cᶜ = 1 := by
    rw [measureReal_add_measureReal_compl hC, probReal_univ]
  have hd : 0 < μ.real Cᶜ := by linarith [h.lt_one]
  have split : ∀ S : Set Ω, μ.real S = μ.real (S ∩ C) + μ.real (S ∩ Cᶜ) := by
    intro S
    rw [← Set.diff_eq, measureReal_inter_add_diff hC]
  unfold PosCorr
  rw [split A, split B, split (A ∩ B)]
  exact reichenbach_real h.pos hd hsum h.screens h.screens_compl h.raisesA h.raisesB

/-- Contrapositive: events that are not positively correlated have no
Reichenbachian common cause. -/
theorem no_commonCause_of_not_posCorr [IsProbabilityMeasure μ]
    (hC : MeasurableSet C) (h : ¬ PosCorr μ A B) : ¬ CommonCause μ C A B :=
  fun hc => h (hc.posCorr hC)

/-! ### Dual aspects of a neutral state -/

/-- An event that is neither impossible nor certain is positively
correlated with itself. -/
theorem posCorr_self [IsProbabilityMeasure μ] {S : Set Ω}
    (hpos : 0 < μ.real S) (hlt : μ.real S < 1) : PosCorr μ S S := by
  unfold PosCorr
  rw [Set.inter_self]
  nlinarith

/-- **Locked aspects correlate.** On a probability space of neutral states
with aspect maps `ψ` and `φ`, a mental event and a physical event that are
two readings of the same neutral states are positively correlated. No
causal structure enters. -/
theorem locked_aspects_posCorr {U M P : Type*} [MeasurableSpace U]
    {ν : Measure U} [IsProbabilityMeasure ν] (ψ : U → M) (φ : U → P)
    (EM : Set M) (EP : Set P) (lock : ψ ⁻¹' EM = φ ⁻¹' EP)
    (hpos : 0 < ν.real (ψ ⁻¹' EM)) (hlt : ν.real (ψ ⁻¹' EM) < 1) :
    PosCorr ν (ψ ⁻¹' EM) (φ ⁻¹' EP) := by
  rw [← lock]
  exact posCorr_self hpos hlt

/-- **The neutral state screens off.** Restricted to a single neutral state
`u`, any two events satisfy the screening-off equation. -/
theorem singleton_screens (u : Ω) (A B : Set Ω) :
    μ.real (A ∩ B ∩ {u}) * μ.real {u} = μ.real (A ∩ {u}) * μ.real (B ∩ {u}) := by
  have key : ∀ S : Set Ω, u ∈ S → S ∩ {u} = {u} :=
    fun S h => Set.inter_eq_right.2 (Set.singleton_subset_iff.2 h)
  have key0 : ∀ S : Set Ω, u ∉ S → S ∩ {u} = ∅ :=
    fun S h => Set.inter_singleton_eq_empty.2 h
  by_cases hA : u ∈ A
  · by_cases hB : u ∈ B
    · rw [key (A ∩ B) ⟨hA, hB⟩, key A hA, key B hB]
    · rw [key0 (A ∩ B) (fun h => hB h.2), key0 B hB]
      simp
  · rw [key0 (A ∩ B) (fun h => hA h.1), key0 A hA]
    simp

/-! ### Bridge to the counting layer -/

open PauliJung in
/-- The counting definition of positive correlation in the core package is
positive correlation of relative frequencies. -/
theorem posCorr_count_iff {α : Type} (l : List α) (e f : α → Bool)
    (hN : 0 < l.length) :
    PauliJung.PosCorr l e f ↔
      (count l e : ℝ) / l.length * ((count l f : ℝ) / l.length)
        < (count l (fun x => e x && f x) : ℝ) / l.length := by
  have hN' : (0 : ℝ) < l.length := by exact_mod_cast hN
  have e2 : (count l (fun x => e x && f x) : ℝ) / l.length
      = (count l (fun x => e x && f x) * l.length : ℝ) / (l.length * l.length) := by
    rw [mul_div_mul_right _ _ hN'.ne']
  rw [div_mul_div_comm, e2, div_lt_div_iff_of_pos_right (mul_pos hN' hN')]
  unfold PauliJung.PosCorr
  exact_mod_cast Iff.rfl

open PauliJung in
/-- Likewise for independence. -/
theorem indep_count_iff {α : Type} (l : List α) (e f : α → Bool)
    (hN : 0 < l.length) :
    PauliJung.Indep l e f ↔
      (count l e : ℝ) / l.length * ((count l f : ℝ) / l.length)
        = (count l (fun x => e x && f x) : ℝ) / l.length := by
  have hN' : (0 : ℝ) < l.length := by exact_mod_cast hN
  have e2 : (count l (fun x => e x && f x) : ℝ) / l.length
      = (count l (fun x => e x && f x) * l.length : ℝ) / (l.length * l.length) := by
    rw [mul_div_mul_right _ _ hN'.ne']
  rw [div_mul_div_comm, e2, div_left_inj' (mul_pos hN' hN').ne']
  unfold PauliJung.Indep
  exact_mod_cast Iff.rfl

end PauliJungProb
