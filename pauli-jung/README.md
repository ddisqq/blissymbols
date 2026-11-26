# Pauli–Jung synchronicity in Lean 4

A machine-checked formalization of the Pauli–Jung dual-aspect conjecture and
Jung's notion of synchronicity ("meaningful coincidence" without causal
connection). Core Lean 4 only, no Mathlib, no `sorry`.

Loosely based on H. Atmanspacher, "The Pauli–Jung Conjecture and Its
Relatives: A Formally Augmented Outline", *Open Philosophy* 3 (2020), and
Jung & Pauli, *The Interpretation of Nature and the Psyche* (1952).

This formalizes the *logical structure* of the conjecture. It says nothing
about whether synchronicities occur.

## Build

    lake build        # Lean 4.26.0, pinned in lean-toolchain

A successful build checks every proof and the axiom audit.

## The picture

- A psychophysically neutral reality `U` (the *unus mundus*); each neutral
  state has a mental aspect `ψ u` and a physical aspect `φ u`.
- Causation relates manifest (mental or physical) states only.
- Archetypes, constellated in a neutral state, give both aspects a meaning.
- A **meaningful coincidence** is an aspect pair with a shared archetype.
  A **synchronicity** is a meaningful coincidence with no causal link:
  no path either way and no common cause.

## Modules

| Module | Contents |
|---|---|
| `PauliJung.Core` | paths, `Model`, `CausallyLinked`, `MeaningfulCoincidence`, `Synchronicity`, Reichenbach, reduction, lawlike/sporadic |
| `PauliJung.Frequency` | counts, `PosCorr`, `Indep`, `ScreensOff`, `StatReichenbach`, `ContentSynchronicity` |
| `PauliJung.Intervention` | `withCauses`, `exploit`, fragility under added causes |
| `PauliJung.Models` | small worlds separating the notions |
| `PauliJung.Cases` | ten canonical cases and the `scorecard` theorem |
| `PauliJung.Audit` | axiom audit of the headline theorems |

## Main results

| Theorem | Statement |
|---|---|
| `no_sync_under_reichenbach` | if every aspect pair is causally linked, there is no synchronicity |
| `noLink_of_separated` | states in different sealed components are not linked |
| `noLink_iff_ancestral` | two distinct events are unlinked iff their causal pasts are disjoint (sound and complete) |
| `sync_iff_ancestral` | synchronicity = meaningful coincidence + disjoint causal pasts |
| `sync_no_signal`, `sync_no_backsignal` | a synchronicity cannot steer matter by mind or mind by matter |
| `sync_antitone` | adding causes never creates a synchronicity |
| `lucadou` | using a synchronicity as a signal keeps its meaning and ends it |
| `locked_aspects_correlate` | locked aspects are positively correlated |
| `stat_reichenbach_fails_of_corr` | correlation in a causeless world refutes the statistical Reichenbach principle |
| `neutral_screens_off` | conditional on the neutral state, mind and matter are independent |
| `ground_without_cause` | such a correlation has no cause but is screened off by the neutral level |
| `sync_without_any_reduction` | synchronicity with neither aspect reducible to the other |
| `meaning_without_sync` | worlds with meaningful coincidences and no synchronicity |
| `strict_not_content`, `iching_content_sync` | strict and content-level synchronicity are logically independent |

## The ten cases

| Case | Strict synchronicity? | Key theorem |
|---|---|---|
| Scarab | yes, even with a common observer | `scarab_sync`, `scarab_collider_sync` |
| Pauli effect | yes | `pauli_effect_sync` |
| Birds at the death | yes | `birds_sync` |
| Swedenborg's fire | yes | `swedenborg_sync` |
| Plum pudding | 2 of 3 episodes | `pudding_dinner_sync`, `pudding_boyhood_not_sync` |
| April fish | no, per encounter | `fish_not_sync_individually` |
| Room 137 | yes, not his physics | `lawlike_not_everywhere_sync` |
| I Ching | no; content-level yes | `iching_not_strict_sync`, `iching_content_sync` |
| Rhine | statistical | `rhine_refutes_stat_reichenbach`, `rhine_ground` |
| Astrology | statistical, sporadic | `astro_sporadic` |

"Yes" means: synchronistic *in the stated model* of the anecdote. The causal
edges of each model are modelling choices. Numbers in the April-fish, I
Ching, Rhine and astrology cases are illustrative, not historical data.

## Limits

- Probability is finite-ensemble frequency; there is no measure theory.
- `neutral_screens_off` holds for any model: it records that the neutral
  level can always play the statistical role of a common cause, not that it
  explains any particular correlation.
- The April-fish clustering is only treated through chance baselines.
