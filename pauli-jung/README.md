# Pauli–Jung synchronicity in Lean 4

A machine-checked formalization of the Pauli–Jung dual-aspect conjecture and
Jung's notion of synchronicity ("meaningful coincidence" without causal
connection). Core Lean 4 only, no Mathlib, no `sorry`.

Loosely based on H. Atmanspacher, "The Pauli–Jung Conjecture and Its
Relatives: A Formally Augmented Outline", *Open Philosophy* 3 (2020), and
Jung & Pauli, *The Interpretation of Nature and the Psyche* (1952).

This formalizes the *logical structure* of the conjecture. It says nothing
about whether synchronicities occur.

## Build and run

    lake build            # Lean 4.26.0, pinned in lean-toolchain
    lake exe paulijung                          # analyse the built-in cases
    lake exe paulijung examples/bookcase.world  # analyse a world file

A successful build checks every proof and the axiom audit. The executable
runs the verified decision procedure on each case and prints the causal
past of both events, whether the pair is meaningful, and the verdict. CI
(`.github/workflows/pauli-jung.yml` at the repo root) runs both.

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
| `PauliJung.Positions` | parallelism, epiphenomenalism, interactionism, complementarity |
| `PauliJung.Morphisms` | `Hom` between worlds; synchronicity is reflected |
| `PauliJung.Decide` | verified decision procedure for causal links and synchronicity in finite worlds |
| `PauliJung.Series` | chance baselines, look-elsewhere, the April fish as a cluster |
| `PauliJung.Models` | small worlds separating the notions |
| `PauliJung.Cases` | ten canonical cases and the `scorecard` theorem |
| `PauliJung.Typology` | Jung's three kinds, time and place, no retrocausation |
| `PauliJung.Applications` | every case re-decided by computation; cases among the positions |
| `PauliJung.MoreCases` | fox, stopped clock, Kammerer's series, the bookcase |
| `PauliJung.Dynamics` | trajectories, decline effect, recurrence |
| `PauliJung.Historical` | figures as reported by Jung and Rhine |
| `PauliJung.Script` | the world-file format behind `paulijung FILE` |
| `PauliJung.Symbols` | the cases as Blissymbol sentences, link symbol computed from the verdict |
| `Bliss` (library) | the Blissymbol database in Lean: well-formedness, `flatten`, `expandWord` |
| `PauliJung.Audit` | axiom audit of the headline theorems |
| `Main` | the `paulijung` executable |
| `BlissExport` | the `blissexport` executable: Lean's data for the 3D viewer in `../bliss3d` |

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
| `Hom.sync_reflect` | a meaningful coincidence whose image under a morphism is synchronistic is itself synchronistic |
| `mem_anc_iff`, `certB_true` | the computed causal past is exactly the causal past; the checker's certificate always holds |
| `Presentation.linked_iff'` | causal links are decided by computation |
| `FullPresentation.sync_iff_syncB` | synchronicity is decidable in finite worlds |
| `scorecard_decided` | every strict verdict in the case table, recomputed by the decision procedure |
| `parallelism_all_sync` | under parallelism every meaningful coincidence is a synchronicity |
| `epiphenomenal_no_control` | under epiphenomenalism mind never steers matter, even indirectly |
| `interaction_with_sync` | synchronicity coexists with two-way mind–matter causation |
| `complementary_nonreductive` | complementary aspects reduce in neither direction |
| `no_retrocausation`, `anticipation_link_iff` | with forward-running causes, a precognitive coincidence is never an effect of its event |
| `three_kinds_realized` | Jung's three kinds (coincident, distant, precognitive) each have a model |
| `locked_aspects_correlate` | locked aspects are positively correlated |
| `stat_reichenbach_fails_of_corr` | correlation in a causeless world refutes the statistical Reichenbach principle |
| `neutral_screens_off` | conditional on the neutral state, mind and matter are independent |
| `ground_without_cause` | such a correlation has no cause but is screened off by the neutral level |
| `AboveChance.of_lower_baseline` | a run that beats one chance rate beats every lower one |
| `exists_max` | every record has a most remarkable entry (look-elsewhere) |
| `sync_decline` | once constellation stops, any early excess over chance is diluted away |
| `sync_recurs` | on a periodic trajectory a synchronicity returns every period |
| `kammerer_acausal_not_sync` | an acausal series without meaning is not a synchronicity |
| `bookcase_second_not_sync` | a fulfilled prediction explained by a common cause |
| `astro_top_never_repeats` | in Jung's reported data each batch favoured a different aspect |
| `Bliss.items_wf`, `Bliss.words_wf` | the Blissymbol database has no missing or circular references |
| `Bliss.itemStrokes_valid` | every symbol flattens to existing primitive paths |
| `link_is_meaning_iff` | a case's Blissymbol sentence says "meaning" exactly when it is a synchronicity |
| `vocabulary_exists` | every symbol used in the sentences is in the database |
| `sync_without_any_reduction` | synchronicity with neither aspect reducible to the other |
| `meaning_without_sync` | worlds with meaningful coincidences and no synchronicity |
| `strict_not_content`, `iching_content_sync` | strict and content-level synchronicity are logically independent |

## The cases

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
| Fox in the wood | yes | `fox_sync` |
| Stopped clock | yes | `clock_sync` |
| Kammerer's series | no: acausal but meaningless | `kammerer_acausal_not_sync` |
| The bookcase | first report yes, prediction no | `bookcase_first_sync`, `bookcase_second_not_sync` |

"Yes" means: synchronistic *in the stated model* of the anecdote. The causal
edges of each model are modelling choices. Numbers in the April-fish, I
Ching, Rhine and astrology cases are illustrative. Figures as reported by
Jung and Rhine are in `PauliJung.Historical`; they were collected from
quotations of the sources, not checked against the printed volumes.

The cases are also written in Blissymbols and shown in 3D: see
[../bliss3d](../bliss3d/README.md).

For a plain-language account see [docs/EXPOSITION.md](docs/EXPOSITION.md).
A measure-theoretic companion lives in `../pauli-jung-prob` (needs Mathlib).

## Limits

- In this package probability is finite-ensemble frequency.
- `neutral_screens_off` holds for any model: it records that the neutral
  level can always play the statistical role of a common cause, not that it
  explains any particular correlation.
- `paulijung FILE` compiles the file to a model and prints the decision
  procedure's value for it (`CWorld.verdict_correct`). The parser and the
  name checks themselves are not verified.
- The decision procedure covers strict synchronicity in finite worlds.
  Which archetype gives meaning to which state is an input of each model,
  not something the system derives.
- The precognitive case in `Typology` is schematic, not a historical
  anecdote. The April-fish day counts in `Series` are illustrative.
