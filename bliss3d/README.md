# Blissymbols in depth

A 3D reading of the Blissymbol set, driven by Lean.

Open `index.html` in a browser (it loads three.js from a CDN).

- Every character is drawn as tubes in space from its primitive paths.
- The Pauli–Jung cases appear as Blissymbol sentences: the mental symbol on
  a front sheet, the physical one on a back sheet, the archetype above. An
  amber pair of lines from the archetype marks a synchronicity; a red bar
  through the depth marks a causal link.
- Any of the 1,150 characters and 4,675 words can be looked up and turned.

## Where the data comes from

| File | Made by | From |
|---|---|---|
| `bliss3d_paths.js` | `node pauli-jung/tools/gen_bliss_lean.js` | `blissdata_chars.js` (geometry of the 166 primitive paths) |
| `bliss3d_data.js` | `lake exe blissexport` in `pauli-jung/` | Lean: flattened characters, expanded words, sentences with verdicts |

To regenerate after the database changes:

    cd pauli-jung
    node tools/gen_bliss_lean.js          # database -> Bliss/Data.lean and bliss3d_paths.js
    lake build                            # re-checks the database in Lean
    lake exe blissexport > ../bliss3d/bliss3d_data.js

## What Lean guarantees, and what it does not

- No character, shape or word refers to something missing or to itself
  (`Bliss.items_wf`, `Bliss.words_wf`), so each resolves to a finite list of
  strokes or characters (`Bliss.flatten`, `Bliss.expandWord`).
- In each sentence the link symbol is "meaning" exactly when the pair is a
  synchronicity in its model, and "cause" exactly when it is causally
  linked (`link_is_meaning_iff`, `link_is_cause_iff`).
- Every symbol used in the sentences exists in the database
  (`vocabulary_exists`).

Not verified: the JavaScript that turns strokes into geometry, and the
layout of words. The viewer places characters side by side with a fixed gap
and sets indicators above the preceding character; it does not apply the
kerning rules of `blissviewer.js`. Which symbol stands for which event is a
choice made by hand in `pauli-jung/PauliJung/Symbols.lean`.
