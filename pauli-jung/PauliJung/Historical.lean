import PauliJung.Frequency

/-!
# Reported figures

Numbers as reported in the literature, kept apart from the illustrative
numbers used elsewhere. Each is labelled by who reports it. They were
collected from quotations of the sources, not from the printed volumes, so
page references are not given; figures that could not be tied to a source
are left out.

The theorems are arithmetic only. That a tally exceeds a chance rate says
nothing about how the tally was produced, and the experiments' methods are
disputed.
-/

namespace PauliJung

/-! ### Jung's astrological experiment (as reported by Jung, 1952)

Three successive batches of married couples. Jung notes that the figures
were later revised downward by M. Fierz. -/

/-- The three batches of marriages. -/
def astroBatches : List Nat := [180, 220, 83]

/-- 483 marriages in all, i.e. 966 horoscopes. -/
theorem astro_total : astroBatches.sum = 483 ∧ 2 * astroBatches.sum = 966 := by decide

/-- The classical marriage aspects that came out on top. -/
inductive Aspect
  | sunMoonConj | moonMoonConj | moonAscConj
  deriving DecidableEq, Repr

/-- The most frequent aspect in each batch. -/
def astroTop : Fin 3 → Aspect
  | 0 => .sunMoonConj
  | 1 => .moonMoonConj
  | 2 => .moonAscConj

/-- Its reported frequency, in parts per thousand (10 %, 10.9 %, 9.6 %). -/
def astroTopPermille : Fin 3 → Nat
  | 0 => 100
  | 1 => 109
  | 2 => 96

/-- **The maximum moved.** Each batch favoured a *different* aspect: the
effect did not replicate as the same effect. -/
theorem astro_top_never_repeats : ∀ i j : Fin 3, astroTop i = astroTop j → i = j := by
  decide

/-- In the first batch the sun–moon conjunction occurred 18 times in 180
(10 %), against 8.4 for Jung's comparison figure. -/
theorem astro_first_batch_reported :
    18 * 1000 = astroTopPermille 0 * 180 ∧ AboveChance 18 180 84 1800 := by decide

/-! ### Rhine's card experiments -/

/-- The deck: 25 cards, 5 symbols, so 5 hits per run by chance. -/
theorem zener_chance : 25 / 5 = 5 := by decide

/-- As reported by Rhine (1934): an early series of 800 trials with 207
hits, which is above the chance rate of one in five... -/
theorem rhine_800 : AboveChance 207 800 1 5 := by decide

/-- ...and averages between 6.4 and 6.5 hits per 25, the "6.5" that Jung
quotes. (Jung describes it as 800 guesses per subject; in Rhine it is the
total of one early series.) -/
theorem rhine_800_average : 64 * 800 < 207 * 25 * 10 ∧ 207 * 25 * 10 < 65 * 800 := by
  decide

/-- As reported by Jung: one subject once named all 25 cards; the chance of
that is one in `5 ^ 25`, the figure Jung prints. -/
theorem zener_all_25 : 5 ^ 25 = 298023223876953125 := by decide

/-- From secondary sources: the Pearce–Pratt distance series, 558 hits in
1850 trials where chance expects 370. -/
theorem pearce_pratt : 1850 / 5 = 370 ∧ AboveChance 558 1850 1 5 := by decide

/-- From secondary sources: the totals of the 1934 monograph, 24 364 hits in
85 724 trials. -/
theorem rhine_1934_total : AboveChance 24364 85724 1 5 := by decide

end PauliJung
