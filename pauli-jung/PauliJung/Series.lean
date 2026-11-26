import PauliJung.Frequency

/-!
# Series and clusters

Runs of similar events (Kammerer's "seriality", Jung's April fish) are not
synchronicities event by event. Whether a *cluster* is remarkable depends on
two things only: the chance baseline, and whether the cluster was picked out
after the fact.
-/

namespace PauliJung

/-- **The verdict follows the baseline.** A run that beats one chance rate
beats every lower one. -/
theorem AboveChance.of_lower_baseline {hits n num den num' den' : Nat}
    (hd' : 0 < den') (hlow : num' * den ≤ num * den')
    (h : AboveChance hits n num den) : AboveChance hits n num' den' := by
  unfold AboveChance at *
  apply Nat.lt_of_mul_lt_mul_right (a := den)
  calc num' * n * den = num' * den * n := Nat.mul_right_comm _ _ _
    _ ≤ num * den' * n := Nat.mul_le_mul_right _ hlow
    _ = num * n * den' := Nat.mul_right_comm _ _ _
    _ < hits * den * den' := Nat.mul_lt_mul_of_pos_right h hd'
    _ = hits * den' * den := Nat.mul_right_comm _ _ _

/-- Conversely, a run that fails against one baseline fails against every
higher one. -/
theorem not_aboveChance_of_higher_baseline {hits n num den num' den' : Nat}
    (hd : 0 < den) (hhigh : num * den' ≤ num' * den)
    (h : ¬ AboveChance hits n num den) : ¬ AboveChance hits n num' den' :=
  fun h' => h (h'.of_lower_baseline hd hhigh)

/-- **Look-elsewhere.** Every non-empty record has a most remarkable entry.
That some day stands out is therefore no evidence of anything. -/
theorem exists_max : ∀ l : List Nat, l ≠ [] → ∃ d ∈ l, ∀ e ∈ l, e ≤ d
  | [], h => absurd rfl h
  | [x], _ => ⟨x, by simp, by simp⟩
  | x :: y :: ys, _ => by
    obtain ⟨d, hd, hmax⟩ := exists_max (y :: ys) (by simp)
    rcases Nat.le_total x d with hxd | hdx
    · refine ⟨d, List.mem_cons_of_mem _ hd, ?_⟩
      intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact hxd
      · exact hmax e he
    · refine ⟨x, by simp, ?_⟩
      intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact Nat.le_refl _
      · exact Nat.le_trans (hmax e he) hdx

/-! ### The April fish as a cluster

Fish motifs noticed per day over ten days. **Illustrative numbers.** -/

def fishDays : List Nat := [6, 1, 0, 2, 1, 0, 1, 1, 0, 1]

/-- The fish day is the most remarkable day on record... -/
theorem fish_day_is_max : 6 ∈ fishDays ∧ ∀ e ∈ fishDays, e ≤ 6 := by decide

/-- ...and it does beat the record's own daily average (13 motifs in 10
days)... -/
theorem fish_day_above_average : AboveChance 6 1 13 10 := by decide

/-- ...but one remarkable day in ten is exactly what a one-in-ten event
predicts. At the level of days there is no excess to explain. -/
theorem fish_cluster_at_chance :
    ¬ AboveChance (count fishDays (fun d => decide (6 ≤ d))) fishDays.length 1 10 := by
  decide

end PauliJung
