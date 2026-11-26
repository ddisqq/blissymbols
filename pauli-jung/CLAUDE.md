# Pauli–Jung synchronicity in Lean 4: working notes

Core-Lean-4 formalization (no Mathlib) of the Pauli–Jung dual-aspect
conjecture and synchronicity. See `README.md` for the module map, theorem
list and scorecard.

## Status
Builds with Lean 4.26.0, no `sorry`, no warnings. `PauliJung/Audit.lean`
pins the axioms of the headline theorems with `#guard_msgs`; if a proof
change alters them, update the expected message there deliberately.

## Build
```
lake build
```
If elan cannot reach its release mirror, download
`lean-4.26.0-linux.zip` from the lean4 GitHub releases, unzip it, and put
its `bin` on `PATH`.

## Conventions
- Don't weaken theorem statements to make them build; fix the proofs.
- Case models are `@[reducible]` so tactics can see through `W.M`, `W.P`.
- `sep_tac` certifies sealed components; `anc_tac`/`dis_tac` certify
  disjoint causal pasts (use these when the events share a common effect).
- Illustrative numbers (fish, I Ching trials, Rhine, astrology) must stay
  labelled as illustrative.

## Possible next steps
- A cluster-level treatment of the April-fish series (an ensemble of days).
- A decidable `CausallyLinked` for finite models, so cases are classified
  by `decide` instead of hand-supplied certificates.
- Historical data for the Rhine and astrology cases, if sourced.
