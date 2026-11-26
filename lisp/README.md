# bliss: Blissymbols for Common Lisp

A Common Lisp library that puts the Blissymbol database to work in programs: look up symbols and
words by English name, see what a word is written with, get its layout and SVG, and use Blisswords
as identifiers in code.

Tested with SBCL 2.2.9. It has no dependencies beyond the Common Lisp standard library.

## Loading

```lisp
(push #p"/path/to/blissymbols/lisp/" asdf:*central-registry*)
(asdf:load-system "bliss")
(in-package #:bliss)
```

Or without ASDF: `(load "/path/to/blissymbols/lisp/bliss.lisp")`.

## API

| Function | Returns |
|---|---|
| `(lookup "friend")` | database key `"friend"`, or NIL. Symbols win over composed words; `"on board"` works as well as `"on_board"`. |
| `(english key)` | English names of a key, e.g. `("ability (half sized)")` |
| `(aliases key)` | other English names of a key |
| `(components key)` | direct components of a composed word, as keys (NIL for a symbol) |
| `(base-symbols word)` | the symbols the word is written with, flattened, in writing order (indicators included) |
| `(layout word)` | a `LAYOUT`: `layout-left`, `layout-right`, `layout-top`, `layout-bottom`, and `layout-items` (each a `placed` with `placed-id`, `placed-x`, `placed-y`) |
| `(svg word &key title)` | standalone SVG text, with the viewer's margins and stroke style |
| `(symbol-p key)`, `(word-p key)` | predicates |
| `(symbol-count)`, `(word-count)`, `(all-symbol-keys)`, `(all-word-keys)` | database contents |

`word` is a database key or a list of keys, e.g. `(layout '("sun" "house"))`. Units are Blissymbol units:
a square is 128 units, a drawing is 320 units high.

## Blisswords as identifiers

`enable-bliss-syntax` installs the reader macro `#@"name"`. It reads as a symbol in the package
`BLISS-WORDS`, so Bliss words can be used as keys, tags and identifiers:

```lisp
(bliss:enable-bliss-syntax)

(defun mood-colour (word)
  (case word
    (#@"happy" :yellow)
    (#@"sad" :blue)
    (t :grey)))

(mood-colour '#@"happy")          ; => :YELLOW  (quote the symbol when you pass it as a value)
(bliss:bliss-symbol-key '#@"friend")  ; => "friend"
(bliss:bliss-symbol "friend")         ; => BLISS-WORDS::|friend|, same as #@"friend"
```

`#@` only accepts names that exist in the database and signals an error otherwise, so a typo
fails at read time rather than at run time.

## Tests and demo

```sh
cd lisp
sbcl --script tests/run.lisp        # 107 checks: layouts match the Python port, lookup, reader syntax, SVG
sbcl --script examples/demo.lisp    # tour of the API; writes friend.svg
```

The layout tests compare 15 words against values computed by `tools/bliss_core.py`.

## Files

- `bliss.asd`: ASDF systems `bliss` and `bliss/tests`
- `src/data.lisp`: the database as Lisp literals (**generated** by `tools/build_lisp.py`; do not edit)
- `src/tables.lisp`: hash tables and name indexes
- `src/layout.lisp`: port of `expand_word`, spacing and kerning from `blissviewer.ts`
- `src/svg.lisp`: port of the drawing code, producing standalone SVG
- `src/api.lisp`: the public functions and the `#@` reader macro
- `tests/`: `tests.lisp`, `run.lisp`, and `fixtures.lisp` (**generated**)

To regenerate the data and fixtures after the database changes: `python3 tools/build_lisp.py`.

## Notes

- The SVG text is structurally the same as the viewer's output, with number formatting done in Lisp, so
  byte-for-byte equality with the Python SVG is not guaranteed. Layouts are identical.
- The library does not build 3D models; that stays in the Python tools.
