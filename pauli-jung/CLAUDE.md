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
lake exe paulijung
```
CI: `.github/workflows/pauli-jung.yml` at the repo root runs both.
If elan cannot reach its release mirror, download
`lean-4.26.0-linux.zip` from the lean4 GitHub releases, unzip it, and put
its `bin` on `PATH`.

## Conventions
- Don't weaken theorem statements to make them build; fix the proofs.
- Case models are `@[reducible]` so tactics can see through `W.M`, `W.P`.
- New case models need a `Presentation` and `FullPresentation` in
  `Applications.lean`, a conjunct in `scorecard_decided`, and a row in
  `Main.lean`.
- `sep_tac` certifies sealed components; `anc_tac`/`dis_tac` certify
  disjoint causal pasts (use these when the events share a common effect).
- Illustrative numbers (fish, I Ching trials, Rhine, astrology) must stay
  labelled as illustrative.

## Possible next steps
- Check the figures in `Historical.lean` against the printed volumes and
  add page references.
- A parser-to-`Model` bridge, so world files inherit the correctness proof.
