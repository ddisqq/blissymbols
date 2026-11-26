import PauliJung.Frequency

/-!
# Dynamics: synchronicity along a trajectory

The neutral state evolves; constellation of an archetype becomes an event
in time. Two regimes are separated:

* **transient** constellation, after which synchronicities stop and any
  initial excess over chance is washed out (the *decline effect*);
* **recurrent** dynamics, where a synchronicity on a cycle returns forever,
  i.e. becomes lawlike along the orbit.
-/

namespace PauliJung

variable (W : Model)

/-- The occurrence at neutral state `u` is meaningful: an archetype
constellated *in `u`* gives meaning to both of its aspects. -/
def MeaningfulAt (u : W.U) : Prop :=
  ∃ a, W.constellated a u ∧ W.expressesM a (W.ψ u) ∧ W.expressesP a (W.φ u)

/-- A synchronistic occurrence at `u`. -/
def SyncAt (u : W.U) : Prop :=
  MeaningfulAt W u ∧ ¬ CausallyLinked W (.inl (W.ψ u)) (.inr (W.φ u))

/-- A synchronistic occurrence yields a synchronicity of its two aspects. -/
theorem SyncAt.sync {u : W.U} (h : SyncAt W u) : Synchronicity W (W.ψ u) (W.φ u) := by
  obtain ⟨⟨a, hc, hm, hp⟩, hl⟩ := h
  exact ⟨⟨a, u, hc, rfl, rfl, hm, hp⟩, hl⟩

/-- Time evolution of the neutral state. -/
structure Dynamics (W : Model) where
  step : W.U → W.U

variable {W} (D : Dynamics W)

/-- The trajectory from an initial neutral state. -/
def Dynamics.traj (D : Dynamics W) (u₀ : W.U) : Nat → W.U
  | 0 => u₀
  | t + 1 => D.step (Dynamics.traj D u₀ t)

/-- From time `T` on, no archetype is constellated along the trajectory. -/
def QuietFrom (u₀ : W.U) (T : Nat) : Prop :=
  ∀ t, T ≤ t → ∀ a, ¬ W.constellated a (D.traj u₀ t)

/-- **No constellation, no synchronicity.** -/
theorem no_sync_when_quiet {u₀ : W.U} {T : Nat} (h : QuietFrom D u₀ T)
    {t : Nat} (ht : T ≤ t) : ¬ SyncAt W (D.traj u₀ t) :=
  fun ⟨⟨a, hc, _⟩, _⟩ => h t ht a hc

/-! ### The decline effect -/

/-- Hits in the first `n` steps of a Boolean record. -/
def hitsUpTo (hit : Nat → Bool) (n : Nat) : Nat := count (List.range n) hit

/-- A record that falls silent at `T` never accumulates more than `T` hits. -/
theorem hitsUpTo_le (hit : Nat → Bool) (T : Nat) (h : ∀ t, T ≤ t → hit t = false) :
    ∀ n, hitsUpTo hit n ≤ T
  | 0 => Nat.zero_le _
  | n + 1 => by
    have ih := hitsUpTo_le hit T h n
    unfold hitsUpTo count at *
    rw [List.range_succ, List.filter_append, List.length_append]
    rcases Nat.lt_or_ge n T with hn | hn
    · have h1 : ((List.range n).filter hit).length ≤ n := by
        simpa using List.length_filter_le hit (List.range n)
      have h2 : ([n].filter hit).length ≤ 1 := List.length_filter_le hit [n]
      omega
    · simp [h n hn]
      exact ih

/-- **Decline effect.** If the hits stop at `T`, then against any fixed
chance rate `num / den` the record is no longer above chance once
`T · den ≤ num · n`. An early excess cannot survive a long enough series. -/
theorem decline (hit : Nat → Bool) (T : Nat) (h : ∀ t, T ≤ t → hit t = false)
    {n num den : Nat} (hn : T * den ≤ num * n) :
    ¬ AboveChance (hitsUpTo hit n) n num den := by
  intro ha
  unfold AboveChance at ha
  have := Nat.mul_le_mul_right den (hitsUpTo_le hit T h n)
  omega

/-- The decline effect for synchronicities on a trajectory: with a decidable
hit record that is silent whenever no synchronistic occurrence takes place,
quiet from `T` on implies the record ends up at or below any chance rate. -/
theorem sync_decline {u₀ : W.U} {T : Nat} (hq : QuietFrom D u₀ T)
    (hit : Nat → Bool) (hhit : ∀ t, hit t = true → SyncAt W (D.traj u₀ t))
    {n num den : Nat} (hn : T * den ≤ num * n) :
    ¬ AboveChance (hitsUpTo hit n) n num den :=
  decline hit T
    (fun t ht => by
      cases hh : hit t with
      | false => rfl
      | true => exact absurd (hhit t hh) (no_sync_when_quiet D hq ht))
    hn

/-! ### Recurrence -/

/-- A trajectory that returns to its start repeats itself. -/
theorem traj_add_period {u₀ : W.U} {p : Nat} (hp : D.traj u₀ p = u₀) :
    ∀ t, D.traj u₀ (t + p) = D.traj u₀ t
  | 0 => by rw [Nat.zero_add]; exact hp
  | t + 1 => by
    rw [Nat.add_right_comm]
    show D.step (D.traj u₀ (t + p)) = D.step (D.traj u₀ t)
    rw [traj_add_period hp t]

theorem traj_mul_period {u₀ : W.U} {p : Nat} (hp : D.traj u₀ p = u₀) :
    ∀ k, D.traj u₀ (k * p) = u₀
  | 0 => by rw [Nat.zero_mul]; rfl
  | k + 1 => by rw [Nat.succ_mul, traj_add_period D hp, traj_mul_period hp k]

/-- **Recurrence.** On a periodic trajectory a synchronistic occurrence
returns at every period: it is no longer sporadic but a regularity of the
orbit. Sporadic synchronicity therefore needs a non-recurring neutral
history. -/
theorem sync_recurs {u₀ : W.U} {p : Nat} (hp : D.traj u₀ p = u₀)
    (h : SyncAt W u₀) (k : Nat) : SyncAt W (D.traj u₀ (k * p)) := by
  rw [traj_mul_period D hp k]
  exact h

/-- On a periodic trajectory with a synchronistic start, the trajectory is
never quiet. -/
theorem not_quiet_of_periodic {u₀ : W.U} {p : Nat} (hp : D.traj u₀ p = u₀)
    (hpos : 0 < p) (h : SyncAt W u₀) (T : Nat) : ¬ QuietFrom D u₀ T := by
  intro hq
  have hT : T ≤ T * p := Nat.le_mul_of_pos_right T hpos
  exact no_sync_when_quiet D hq hT (sync_recurs D hp h T)

/-! ### Example: a fading constellation

Trials are numbered `0, 1, 2, …`; the archetype is constellated only in the
first three (initial interest, in Rhine's and Jung's telling). No causes.
**Illustrative.** -/

@[reducible] def fadingW : Model where
  U := Nat
  M := Unit
  P := Unit
  A := Unit
  ψ := fun _ => ()
  φ := fun _ => ()
  causes := fun _ _ => False
  constellated := fun _ t => t < 3
  expressesM := fun _ _ => True
  expressesP := fun _ _ => True

def fadingD : Dynamics fadingW := ⟨Nat.succ⟩

theorem fading_traj : ∀ t, fadingD.traj 0 t = t
  | 0 => rfl
  | t + 1 => by
    show Nat.succ (fadingD.traj 0 t) = t + 1
    rw [fading_traj t]

theorem fading_sync_early : SyncAt fadingW (fadingD.traj 0 2) := by
  rw [fading_traj]
  exact ⟨⟨(), by decide, trivial, trivial⟩, noLink_of_noCause fadingW (fun _ _ h => h) _ _⟩

theorem fading_quiet : QuietFrom fadingD 0 3 := by
  intro t ht a hc
  rw [fading_traj] at hc
  have : t < 3 := hc
  omega

/-- Three hits in the first five trials beat a chance rate of 1/5... -/
theorem fading_early_excess :
    AboveChance (hitsUpTo (fun t => decide (t < 3)) 5) 5 1 5 := by decide

/-- ...and by trial 15 the excess is gone, by the general decline theorem. -/
theorem fading_decline :
    ¬ AboveChance (hitsUpTo (fun t => decide (t < 3)) 15) 15 1 5 :=
  sync_decline fadingD fading_quiet (fun t => decide (t < 3))
    (fun t ht => by
      have h3 : t < 3 := of_decide_eq_true ht
      rw [fading_traj]
      exact ⟨⟨(), h3, trivial, trivial⟩, noLink_of_noCause fadingW (fun _ _ h => h) _ _⟩)
    (by decide)

end PauliJung
