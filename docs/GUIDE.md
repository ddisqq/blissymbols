# Guide to the Blissymbol supporting files

This guide explains what is in the repository beyond the original database, how the new files were made, and how to use them.

## 1. What Blissymbols are, in brief

Blissymbolics is a graphic language of about 1,150 basic symbols (here called *symbols* or *characters*). Meaning is built by combining them:

- **Symbols** are the basic units, such as *sun*, *man (male)*, *house*, *heart*.
- **Indicators** are small marks placed above or after a symbol to change its meaning: for example *indicator (description)* turns a noun into an adjective, *indicator (action)* makes it a verb.
- **Words** are composed of several symbols written left to right, such as *friend* or *habit*. Each word is defined in the database as a list of other words or symbols.
- **Punctuation** (comma, period, question mark, exclamation mark) and **modifiers** (e.g. *minus, no, without*; *intensity*; *more*) follow the rules in `blissviewer.ts`.
- Blissymbolic grammar is simple: there are no articles and no verb "to be". That is why the poem in this repository reads word by word.

## 2. What the database contains

| File | Contents |
|---|---|
| `blissdata_chars.js` | 1,150 symbols with their size, drawing parts (`paths`, `shapes`), spacing (`center`, `kerning_left`, `kerning_right`) |
| `blissdata_words.js` | 4,675 headwords, each with its composition |
| `blissdata.d.ts` | TypeScript description of the two data objects |
| `blissviewer.ts` / `.js` | the reference renderer (drawing rules, word layout, spacing) |
| `download_and_update_blissdata_words.py` | refreshes `blissdata_words.js` from the Språkbanken Karp lexicon |

The database holds **no prose definitions**. The "definition" of a word is its English name(s) plus its composition, and the dictionary in `dictionary/` shows exactly that.

**Note on the refresh:** the task asked for all symbols to be pulled. In this session the Språkbanken servers (svn.spraakdata.gu.se and spraakbanken.gu.se) were unreachable from the sandbox (HTTP 403 from the egress proxy), so the refresh could not run. Everything here is built from the database as committed, whose latest commit is the Karp sync "Word definitions updated from the Karp database". To refresh later, run `python3 download_and_update_blissdata_words.py` from a machine with access, then rebuild (section 6).

## 3. Supporting files

| Folder / file | What it is | How many |
|---|---|---|
| `dictionary/bliss_dictionary.md` | Readable dictionary: every headword, alphabetical, with *also called* names, composition and symbol count | 4,675 entries |
| `dictionary/bliss_dictionary.csv` | The same, for spreadsheets: headword, aliases, composition, base symbols, database key | 4,675 rows |
| `dictionary/symbols_index.csv` | One row per symbol: names, size, number of drawing parts, usage count, file links, mesh statistics | 1,150 rows |
| `svg/NNNN-name.svg` | Original 2D drawing of each symbol, rendered with the same geometry as the viewer | 1,150 files |
| `3d/NNNN-name.glb` | 3D equivalent of each symbol (glTF binary) | 1,150 files |
| `3d/viewer.html` | Interactive 3D viewer: pick a symbol, orbit it, see the original next to it | — |
| `3d/catalog.json` | List of symbols used by the viewer | — |
| `gallery/index.html` | Searchable page showing every symbol, its original and a link to its 3D model | 1,150 cards |
| `poem/` | The poem *After Rain* (`index.html`), with each word as a 2D drawing and a 3D equivalent | 26 words |
| `tools/` | Scripts that produce everything above (section 6) | — |

Usage counts in `symbols_index.csv` (`used_in_headwords`) count how many of the 4,675 headwords contain that symbol, directly or inside a sub-word. The most used symbol appears in 639 headwords; 322 symbols are not used by any headword and only appear as standalone symbols.

Drawing complexity ranges from 1 part (e.g. *a*) to 16 parts (`drawing_parts`).

## 4. How the 2D drawings are made

`tools/bliss_core.py` is a line-by-line port of `blissviewer.ts`:

- Data coordinates have their origin at the bottom of a symbol. The viewer flips them about a height of 320 units (`svg_y = 320 − y`).
- Strokes are 8 units wide with round caps and joins (from `blissviewer.css`). Dots and discs are filled; circles are 8-unit rings.
- Arcs use the SVG endpoint arc rule (`A rx,ry 0 0,0`; `bigarc` uses the large-arc flag), quadratic curves use `Q`.
- Text parts (letters and digits such as *a*, *A*) are drawn at 88 units. The SVG uses the browser font; the 3D version uses Liberation Sans, which has the same metrics as Helvetica/Arial.
- Words are laid out with the viewer's spacing and kerning rules, including indicator placement.

The SVG files carry their own style block, so they display correctly when opened directly.

## 5. How the 3D equivalents are made

1. The 2D drawing is converted to filled outlines: each stroke becomes a 8-unit-wide outline with round ends, each arc is sampled, each glyph is taken from its font outline with counters (holes) respected.
2. The outlines are merged into one shape per symbol.
3. The shape is extruded into a solid slab with a depth of 16 units (two stroke widths).
4. Units: **1 Bliss square = 1 glTF unit**. Y is up, Z is the depth direction. Each model is centred on the origin in X and Y.

Results: 276,608 triangles across all 1,150 models. 1,099 models are fully closed ("watertight"). The other 51 are still solid and display correctly, but a few stroke ends touch at a single point, which leaves a non-manifold edge. This is noted in the `mesh_watertight` column of `symbols_index.csv`.

The 3D models are a flat extrusion of the drawing, not new artwork: they show the same shape as the 2D symbol with real thickness. Word-level 3D equivalents (used in the poem) are made the same way from the whole composition.

## 6. Rebuilding

Requirements: Python 3 with `shapely`, `trimesh`, `numpy`, `scipy`, `mapbox_earcut`, `matplotlib`; Node with Playwright only for the poem pictures.

```sh
python3 tools/build_symbols.py      # svg/, 3d/, dictionary/symbols_index.csv   (about 6 s)
python3 tools/build_dictionary.py   # dictionary/*.md|csv, gallery/index.html, 3d/catalog.json
python3 tools/build_poem.py         # poem/index.html, poem/2d, poem/3d/*.glb, poem/poem.json
node tools/render_poem_3d.js        # poem/3d/*.png (uses Chromium via Playwright)
```

Set `THREE_LOCAL=/path/to/node_modules/three` when running `render_poem_3d.js` offline.

## 7. Using the 3D viewer

The viewer loads three.js from unpkg, so it needs an internet connection. Because browsers block loading models from `file://` pages, serve the repository over HTTP:

```sh
python3 -m http.server 8000
# then open http://localhost:8000/3d/viewer.html   (or ?symbol=0628-man.glb)
```

## 8. Making a new poem

Edit `STANZAS` and `TITLE` in `tools/build_poem.py`. Each token must be the English name of a symbol or word in the database; `build_poem.py` finds the entry and stops with an error if it cannot. Blissymbolic grammar has no articles or "is", so write in that style. Then run the poem steps in section 6.

## 9. Limitations

- The database could not be refreshed from Karp in this session (section 2).
- 3D models are extrusions of the 2D drawings, so they show the form of each symbol but not any depth or shading in the original design.
- 51 of 1,150 models are not closed solids (section 5).
- Text parts in 3D use a font outline, which can differ slightly from the browser's rendering of the same letter.
