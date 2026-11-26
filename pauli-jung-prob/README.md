# Pauli–Jung: measure-theoretic companion

The core package (`../pauli-jung`) models probability by counting in finite
ensembles and uses no libraries. This package restates the statistical part
for an arbitrary probability measure, using Mathlib.

    lake exe cache get    # fetch prebuilt Mathlib
    lake build

## Contents (`PauliJungProb/Basic.lean`)

| Theorem | Statement |
|---|---|
| `CommonCause.posCorr` | Reichenbach's theorem: an event that screens off two others and raises the probability of each makes them positively correlated |
| `no_commonCause_of_not_posCorr` | uncorrelated events have no Reichenbachian common cause |
| `not_posCorr_of_indepSet` | independent events (in Mathlib's sense) are not positively correlated |
| `locked_aspects_posCorr` | two readings of the same neutral states are positively correlated, with no causal structure |
| `singleton_screens` | restricted to one neutral state, any two events satisfy the screening-off equation |
| `posCorr_count_iff`, `indep_count_iff` | the counting definitions of the core package are the frequency instances of the real-valued ones |

Conditional probabilities are written multiplied out, so no statement
divides by zero.
