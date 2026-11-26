import PauliJung.Core

/-!
# Frequencies: correlation, independence, screening-off

Probability is modelled by frequencies in a finite ensemble, so no real
numbers are needed.
-/

namespace PauliJung

variable (W : Model)

/-! ### Counting

`P(e ∧ f) > P(e) P(f)` becomes `#e · #f < #(e ∧ f) · N`. -/

/-- Number of ensemble members satisfying `p`. -/
def count {α : Type} (l : List α) (p : α → Bool) : Nat := (l.filter p).length

/-- Positive correlation of two events in the ensemble. -/
abbrev PosCorr {α : Type} (l : List α) (e f : α → Bool) : Prop :=
  count l e * count l f < count l (fun x => e x && f x) * l.length

/-- Statistical independence of two events in the ensemble:
`P(e ∧ f) = P(e) P(f)`. -/
abbrev Indep {α : Type} (l : List α) (e f : α → Bool) : Prop :=
  count l e * count l f = count l (fun x => e x && f x) * l.length

/-- Independent events are not positively correlated. -/
theorem Indep.not_posCorr {α : Type} {l : List α} {e f : α → Bool}
    (h : Indep l e f) : ¬ PosCorr l e f :=
  fun hc => Nat.lt_irrefl _ (Nat.lt_of_lt_of_eq hc h.symm)

/-- `hits` successes in `n` trials beat the chance rate `num / den`. -/
abbrev AboveChance (hits n num den : Nat) : Prop := num * n < hits * den

theorem filter_congr' {α : Type} (p q : α → Bool) :
    ∀ l : List α, (∀ x ∈ l, p x = q x) → l.filter p = l.filter q
  | [], _ => rfl
  | x :: xs, h => by
    have hx : p x = q x := h x (by simp)
    have ih := filter_congr' p q xs (fun y hy => h y (by simp [hy]))
    cases hq : q x <;> simp [List.filter, hx, hq, ih]

theorem count_congr {α : Type} (l : List α) (p q : α → Bool)
    (h : ∀ x ∈ l, p x = q x) : count l p = count l q := by
  unfold count
  rw [filter_congr' p q l h]

theorem mul_self_lt_mul {c n : Nat} (hc : 0 < c) (h : c < n) : c * c < c * n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = c + k + 1 := ⟨n - c - 1, by omega⟩
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
  omega

/-- Positive correlation is symmetric. -/
theorem PosCorr.symm {α : Type} {l : List α} {e f : α → Bool}
    (h : PosCorr l e f) : PosCorr l f e := by
  unfold PosCorr at *
  rw [count_congr l (fun x => f x && e x) (fun x => e x && f x)
        (fun x _ => by
          show (f x && e x) = (e x && f x)
          cases f x <;> cases e x <;> rfl),
      Nat.mul_comm (count l f) (count l e)]
  exact h

/-- **Locked aspects correlate.** If a mental and a physical event are two
readings of the same neutral states, and the event is neither impossible nor
certain in the ensemble, they are positively correlated. -/
theorem locked_aspects_correlate (ens : List W.U)
    (EM : W.M → Bool) (EP : W.P → Bool)
    (lock : ∀ u ∈ ens, EM (W.ψ u) = EP (W.φ u))
    (hpos : 0 < count ens (fun u => EM (W.ψ u)))
    (hlt : count ens (fun u => EM (W.ψ u)) < ens.length) :
    PosCorr ens (fun u => EM (W.ψ u)) (fun u => EP (W.φ u)) := by
  have h1 : count ens (fun u => EP (W.φ u)) = count ens (fun u => EM (W.ψ u)) :=
    count_congr ens _ _ (fun u hu => (lock u hu).symm)
  have h2 : count ens (fun u => EM (W.ψ u) && EP (W.φ u))
      = count ens (fun u => EM (W.ψ u)) :=
    count_congr ens _ _ (fun u hu => by simp [lock u hu])
  unfold PosCorr
  rw [h1, h2]
  exact mul_self_lt_mul hpos hlt

/-- **Statistical Reichenbach principle** for an ensemble: every positive
mind–matter correlation is witnessed by a causal link somewhere. -/
def StatReichenbach (ens : List W.U) : Prop :=
  ∀ (EM : W.M → Bool) (EP : W.P → Bool),
    PosCorr ens (fun u => EM (W.ψ u)) (fun u => EP (W.φ u)) →
    ∃ u ∈ ens, CausallyLinked W (.inl (W.ψ u)) (.inr (W.φ u))

/-- **Correlation without causation.** In a causally empty world, any positive
mind–matter correlation refutes the statistical Reichenbach principle. -/
theorem stat_reichenbach_fails_of_corr (hW : ∀ x y, ¬ W.causes x y)
    (ens : List W.U) (EM : W.M → Bool) (EP : W.P → Bool)
    (hc : PosCorr ens (fun u => EM (W.ψ u)) (fun u => EP (W.φ u))) :
    ¬ StatReichenbach W ens := by
  intro h
  obtain ⟨u, _, hl⟩ := h EM EP hc
  exact noLink_of_noCause W hW _ _ hl

/-- In particular, a non-trivial locked pair refutes it. -/
theorem stat_reichenbach_fails (hW : ∀ x y, ¬ W.causes x y)
    (ens : List W.U) (EM : W.M → Bool) (EP : W.P → Bool)
    (lock : ∀ u ∈ ens, EM (W.ψ u) = EP (W.φ u))
    (hpos : 0 < count ens (fun u => EM (W.ψ u)))
    (hlt : count ens (fun u => EM (W.ψ u)) < ens.length) :
    ¬ StatReichenbach W ens :=
  stat_reichenbach_fails_of_corr W hW ens EM EP
    (locked_aspects_correlate W ens EM EP lock hpos hlt)

/-! ### Constant events and screening-off -/

theorem count_true {α : Type} (l : List α) : count l (fun _ => true) = l.length := by
  simp [count]

theorem count_false {α : Type} (l : List α) : count l (fun _ => false) = 0 := by
  simp [count]

/-- An event that is constant on the ensemble is independent of everything. -/
theorem indep_of_const_left {α : Type} (l : List α) (e f : α → Bool) (b : Bool)
    (h : ∀ x ∈ l, e x = b) : Indep l e f := by
  unfold Indep
  cases b with
  | false =>
    rw [count_congr l e (fun _ => false) h,
        count_congr l (fun x => e x && f x) (fun _ => false)
          (fun x hx => by simp [h x hx]),
        count_false]
    simp
  | true =>
    rw [count_congr l e (fun _ => true) h,
        count_congr l (fun x => e x && f x) f (fun x hx => by simp [h x hx]),
        count_true, Nat.mul_comm]

/-- `c` **screens off** `e` from `f`: within each stratum of `c` the two
events are independent. This is the statistical signature Reichenbach
required of a common cause. -/
def ScreensOff {α : Type} (l : List α) (c e f : α → Bool) : Prop :=
  Indep (l.filter c) e f ∧ Indep (l.filter (fun x => !c x)) e f

/-- **The neutral state screens off.** Conditional on the underlying neutral
state, the mental and the physical aspect are always independent: every
mind–matter correlation is statistically accounted for at the neutral level,
whether or not any manifest cause exists. The *unus mundus* plays the formal
role of Reichenbach's common cause without being a cause. -/
theorem neutral_screens_off [DecidableEq W.U] (ens : List W.U)
    (EM : W.M → Bool) (EP : W.P → Bool) (u : W.U) :
    Indep (ens.filter (fun v => v == u))
      (fun v => EM (W.ψ v)) (fun v => EP (W.φ v)) := by
  apply indep_of_const_left _ _ _ (EM (W.ψ u))
  intro v hv
  have hvu : v = u := by simpa using (List.mem_filter.1 hv).2
  rw [hvu]

/-- **Correlation with a ground but without a cause.** In a causally empty
world a positive mind–matter correlation has no causal explanation
(`StatReichenbach` fails), yet it is screened off by the neutral state. -/
theorem ground_without_cause [DecidableEq W.U] (hW : ∀ x y, ¬ W.causes x y)
    (ens : List W.U) (EM : W.M → Bool) (EP : W.P → Bool)
    (hc : PosCorr ens (fun u => EM (W.ψ u)) (fun u => EP (W.φ u))) :
    ¬ StatReichenbach W ens ∧
      ∀ u, Indep (ens.filter (fun v => v == u))
        (fun v => EM (W.ψ v)) (fun v => EP (W.φ v)) :=
  ⟨stat_reichenbach_fails_of_corr W hW ens EM EP hc,
   neutral_screens_off W ens EM EP⟩

/-! ### Content-level synchronicity

The strict definition forbids any causal path. In divination (the I Ching)
and in some series the *occurrence* of the physical event is plainly caused
by the mental one: asking makes the coins fall. What is claimed to be acausal
is the fit between the *content* of the question and the outcome. -/

/-- **Content synchronicity** at `u` in an ensemble of trials: a meaningful
coincidence in which the mental content `EM` and the physical outcome `EP`
both occur, while across the ensemble the content does not raise the
frequency of the outcome. A causal path from `ψ u` to `φ u` is allowed. -/
def ContentSynchronicity (ens : List W.U) (EM : W.M → Bool) (EP : W.P → Bool)
    (u : W.U) : Prop :=
  u ∈ ens ∧ MeaningfulCoincidence W (W.ψ u) (W.φ u) ∧
  EM (W.ψ u) = true ∧ EP (W.φ u) = true ∧
  ¬ PosCorr ens (fun v => EM (W.ψ v)) (fun v => EP (W.φ v))

/-- A content synchronicity is a meaningful coincidence. -/
theorem ContentSynchronicity.meaningful {ens : List W.U} {EM : W.M → Bool}
    {EP : W.P → Bool} {u : W.U} (h : ContentSynchronicity W ens EM EP u) :
    MeaningfulCoincidence W (W.ψ u) (W.φ u) :=
  h.2.1

/-- **Statistical no-signalling.** A content synchronicity gives no
statistical handle: choosing the content does not make the outcome more
frequent. -/
theorem ContentSynchronicity.no_stat_signal {ens : List W.U} {EM : W.M → Bool}
    {EP : W.P → Bool} {u : W.U} (h : ContentSynchronicity W ens EM EP u) :
    ¬ PosCorr ens (fun v => EM (W.ψ v)) (fun v => EP (W.φ v)) :=
  h.2.2.2.2

/-- Locked aspects are never a content synchronicity: there the content
*does* track the outcome. -/
theorem not_content_sync_of_locked (ens : List W.U)
    (EM : W.M → Bool) (EP : W.P → Bool)
    (lock : ∀ u ∈ ens, EM (W.ψ u) = EP (W.φ u))
    (hpos : 0 < count ens (fun u => EM (W.ψ u)))
    (hlt : count ens (fun u => EM (W.ψ u)) < ens.length) (u : W.U) :
    ¬ ContentSynchronicity W ens EM EP u :=
  fun h => h.no_stat_signal W (locked_aspects_correlate W ens EM EP lock hpos hlt)

end PauliJung
