# Synchronicity, formally: a reader's guide

This guide explains what the Lean development in this folder says, in plain
terms, for readers who do not read Lean. Names in `code font` are the
theorems you can look up.

## What is being formalized

In 1952 the psychologist C. G. Jung and the physicist Wolfgang Pauli
published a joint book proposing that some coincidences between an inner
state and an outer event are connected by *meaning* and not by *cause*.
Jung called these **synchronicities**. Behind the idea stands a
philosophical picture, later called the Pauli–Jung conjecture:

- there is one underlying reality that is neither mental nor physical;
- the mental and the physical are two aspects of it;
- ordering patterns of that reality (Jung's *archetypes*) can show up in
  both aspects at once.

The formalization turns this picture into definitions precise enough for a
proof checker, and then asks what follows.

**It does not show that synchronicities happen.** It shows what the claim
commits you to, what it excludes, and which familiar stories fit the
definition once you say exactly what caused what.

## The definitions

A **world** has neutral states, mental states, physical states and
archetypes. Every neutral state has a mental aspect and a physical aspect.
Causes run between mental and physical states, in any combination: a sight
can cause a thought, a decision can cause a movement.

Two events are **causally linked** if one leads to the other through a
chain of causes, or if some third event leads to both. This is the usual
list of causal explanations for a correlation.

A pair of a mental and a physical state is a **meaningful coincidence** if
they are the two aspects of one neutral state, and an archetype active in
that state gives meaning to both.

A **synchronicity** is a meaningful coincidence that is not causally linked.

## What follows

**It excludes a principle most science assumes.** If every pair of aspects
has a causal explanation, there are no synchronicities
(`no_sync_under_reichenbach`). The conjecture is therefore a real claim: it
needs some correlations that causes do not explain.

**It is not signalling.** A synchronicity cannot be used by the mind to
steer matter or the other way round (`sync_no_signal`). If you add the
causal channel that would let you use one, the coincidence keeps its meaning
and stops being a synchronicity (`lucadou`). More generally, learning about
more causes can only remove synchronicities, never add them
(`sync_antitone`, `Hom.sync_reflect`).

**There is an exact test.** Two events are free of any causal link exactly
when their causal pasts do not overlap (`noLink_iff_ancestral`). Sharing a
common *effect* does not count: two events noticed by the same observer are
not thereby linked. For finite worlds this test is a computation, proved
correct (`FullPresentation.sync_iff_syncB`), so verdicts can be calculated
instead of argued.

**It is not parallelism, and not dualism.** If mind and matter never
interact, *every* meaningful coincidence is a synchronicity
(`parallelism_all_sync`); Jung's are meant to be rare. And synchronicity is
compatible with ordinary two-way interaction between mind and matter
(`interaction_with_sync`). Neither aspect needs to be reducible to the other
(`sync_without_any_reduction`).

**Time.** If causes only run forward, a mental state that precedes the
event it matches cannot have been caused by that event
(`no_retrocausation`). A "precognitive" coincidence is then either brought
about by the mental state, or due to a common cause, or a synchronicity.

**Statistics.** Two aspects that always agree are correlated
(`locked_aspects_correlate`), with no cause needed. Conditional on the
neutral state they are independent (`neutral_screens_off`). This shows that
the neutral level *can* play the statistical role of a common cause; it does
not show that it explains any particular correlation, since the statement
holds in every world by construction.

**Fading and recurrence.** If the archetype stops being active, the hits
stop, and any early excess over chance is eventually diluted away
(`sync_decline`). If instead the underlying state cycles, a synchronicity on
the cycle comes back every time and is no longer sporadic (`sync_recurs`).

**Series.** Whether a run of similar events is remarkable depends only on
the chance rate you compare it with (`AboveChance.of_lower_baseline`), and
every record has a most striking entry (`exists_max`), so finding one is not
evidence.

**A second kind.** In divination the question plainly causes the answer to
appear: asking makes the coins fall. What is claimed to be acausal is the
fit between what was asked and what came up. This is captured separately as
*content synchronicity*, and neither kind implies the other
(`strict_not_content`, `iching_content_sync`).

## The cases

Fourteen stories are modelled. For each, the causal arrows are written down
explicitly, and the verdict is computed.

| Story | Verdict in the model |
|---|---|
| Jung's patient and the scarab | synchronicity, also when Jung observes both |
| The Pauli effect | synchronicity |
| Birds at a death | synchronicity |
| Swedenborg and the Stockholm fire | synchronicity; the later news is causal |
| The plum pudding | two episodes yes, the first (a gift) no |
| The April fish | no single encounter; as a ten-day cluster, at chance |
| Room 137 | the room yes, Pauli's physics no |
| The I Ching | not strictly; content-level yes |
| Rhine's card guessing | statistical only |
| Jung's astrology experiment | statistical; the favoured aspect changed in every batch |
| The fox in the wood | synchronicity |
| The clock that stops at a death | synchronicity |
| Kammerer's series | no: nothing links the events, and nothing gives them meaning |
| The bookcase (Jung and Freud) | first report yes; the fulfilled prediction no (common cause) |

Two things are worth noticing. In the bookcase story, the half that sounds
most uncanny, the prediction coming true, is the half with an ordinary
explanation in the sceptic's model. And Kammerer's series shows that being
causally unconnected is not enough: without meaning there is only a run.

## How much to read into a verdict

Each verdict is conditional on its model. Whoever draws the arrows decides
the answer: add an arrow from the dream to the beetle and the scarab case
is no longer a synchronicity. What the formalization contributes is that
this is now explicit. A sceptic and a believer who disagree about a story
must disagree about a specific arrow or a specific assignment of meaning,
and the program will tell them what follows from either choice.

Which archetype gives meaning to which event is likewise an input. Nothing
here derives meaning from anything else.

The numbers in the Rhine, astrology, April-fish and I Ching ensembles are
illustrative unless they appear in `PauliJung/Historical.lean`, which holds
figures as reported by Jung and by Rhine, each labelled with who reports it.
Those were collected from quotations of the sources, not checked against
the printed volumes.

## Trying your own case

Describe a world in a text file and run the program on it:

    lake exe paulijung examples/bookcase.world

The format is explained at the top of `PauliJung/Script.lean`, and
`examples/` has files to copy from.

## Sources

- C. G. Jung and W. Pauli, *The Interpretation of Nature and the Psyche* (1952).
- H. Atmanspacher, "The Pauli–Jung Conjecture and Its Relatives: A Formally
  Augmented Outline", *Open Philosophy* 3 (2020).
- J. B. Rhine, *Extra-Sensory Perception* (1934).
