"""
Build the poem "After Rain" from Blissymbols.

Each token of the poem is a Blisswords id from the database (a single symbol or a word
composed of several). For every token we write:

  poem/2d/NN-<token>.svg   the original drawing (same geometry as the viewer)
  poem/3d/NN-<token>.glb   the 3D equivalent: the same composition extruded into a solid

and poem/poem.json, which the page and the 3D render step read.
Run:  python3 tools/build_poem.py   (then tools/render_poem_3d.js makes the 3D PNGs)
"""

import glob
import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import bliss_core as bc  # noqa: E402

REPO = bc.REPO

# Each poem: output folder under poem/ (empty = poem/ itself), title, and stanzas.
# Blissymbolic word order: no articles, no "is". Each line lists English names of Blisswords.
POEMS = {
    "after-rain": {
        "folder": "",
        "title": "After Rain",
        "stanzas": [
            ["sun warm water", "bird song"],
            ["friend come home", "heart happy"],
            ["rain go", "no sad"],
            ["star night moon", "time walk see"],
            ["love live open", "hope new day"],
        ],
    },
    "crossing-the-river": {
        "folder": "crossing-the-river",
        "title": "Crossing the River",
        "stanzas": [
            ["bridge river", "night light"],
            ["friend walk go", "warm"],
            ["window home", "light fire"],
            ["sea star", "see"],
            ["wind sleep", "time hope"],
        ],
    },
}


def names_of(key):
    return [n for n in key.split(",") if n]


def resolve(token, chars, words):
    """Find the database id for an English name. Symbols are preferred over composed words."""
    t = token.lower()
    for src in (chars, words):
        exact = [k for k in src if names_of(k) and names_of(k)[0].lower() == t]
        if exact:
            return sorted(exact, key=len)[0]
    for src in (chars, words):
        any_alias = [k for k in src if t in [n.lower() for n in names_of(k)]]
        if any_alias:
            return sorted(any_alias, key=len)[0]
    raise KeyError(f"no Blisswords entry for {token!r}")


def slug(s):
    return re.sub(r"[^A-Za-z0-9]+", "-", s).strip("-").lower()


PAGE_CSS = """
:root{--bg:#fbfaf7;--fg:#161616;--mut:#6b6b6b;--line:#e6e2d9;--card:#fff;--acc:#1f5fbf}
@media (prefers-color-scheme: dark){:root:not([data-theme="light"]){--bg:#141414;--fg:#eee;--mut:#9a9a9a;--line:#2e2e2e;--card:#1d1d1d;--acc:#7fb0ff}}
:root[data-theme="dark"]{--bg:#141414;--fg:#eee;--mut:#9a9a9a;--line:#2e2e2e;--card:#1d1d1d;--acc:#7fb0ff}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--fg);font:17px/1.55 Georgia,"Times New Roman",serif}
main{max-width:880px;margin:0 auto;padding:40px 16px 64px}
h1{font:600 32px/1.2 system-ui,-apple-system,"Helvetica Neue",Arial,sans-serif;margin:0 0 8px}
.lede{color:var(--mut);font:15px/1.5 system-ui,-apple-system,"Helvetica Neue",Arial,sans-serif;margin:0 0 36px}
.stanza{margin:0 0 30px;padding:0 0 0 18px;border-left:2px solid var(--line)}
.line{display:flex;flex-wrap:wrap;align-items:flex-end;gap:14px 18px;margin:0 0 18px}
.token{display:flex;flex-direction:column;align-items:center;width:232px}
.pair{display:grid;grid-template-columns:1fr 1fr;gap:6px;width:100%}
.pair figure{margin:0;background:var(--card);border:1px solid var(--line);border-radius:10px;padding:6px;display:flex;flex-direction:column;align-items:center}
.pair img{height:124px;width:100%;object-fit:contain}
.pair figcaption{font:12px/1 system-ui,-apple-system,sans-serif;color:var(--mut);margin-top:4px}
.pair a{color:inherit;text-decoration:none}
.word{margin-top:6px;font-style:italic;text-align:center}
.key{font:12px/1.3 system-ui,-apple-system,sans-serif;color:var(--mut);text-align:center;word-break:break-word}
.key a{color:var(--acc)}
.notes{margin-top:48px;padding-top:20px;border-top:1px solid var(--line);color:var(--mut);font:14px/1.6 system-ui,-apple-system,sans-serif}
.notes a{color:var(--acc)}
@media (max-width:560px){.token{width:44%}.pair img{height:96px}}
"""


def write_page(out, doc, viewer_href="../3d/viewer.html"):
    import html as H
    parts = []
    for stanza in doc["stanzas"]:
        lines = []
        for line in stanza:
            toks = []
            for tok in line:
                rec = doc["tokens"][tok]
                kind = "symbol" if rec["kind"] == "symbol" else "word"
                key = rec["database_key"].replace("_", " ")
                toks.append(
                    '<div class="token">'
                    '<div class="pair">'
                    f'<figure><img src="{H.escape(rec["svg"])}" alt="{H.escape(tok)}, original drawing"><figcaption>original</figcaption></figure>'
                    f'<figure><a href="{H.escape(rec["glb"])}"><img src="{H.escape(rec["png"])}" alt="{H.escape(tok)}, 3D equivalent"></a>'
                    '<figcaption>3D (.glb)</figcaption></figure>'
                    '</div>'
                    f'<div class="word">{H.escape(tok)}</div>'
                    f'<div class="key">{kind}: {H.escape(key)}</div>'
                    '</div>'
                )
            lines.append('<div class="line">' + "".join(toks) + "</div>")
        parts.append('<section class="stanza">' + "".join(lines) + "</section>")
    page = f"""<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>{H.escape(doc["title"])}</title>
<style>{PAGE_CSS}</style>
</head><body><main>
<h1>{H.escape(doc["title"])}</h1>
<p class="lede">A poem written only in Blisswords: each word is shown as its original Blissymbol drawing
and as a new 3D equivalent extruded from that same drawing. Like Blissymbolics itself, the poem has no
articles and no verb "to be", so it reads word by word. The line under each word gives the English name
and the database entry it comes from.</p>
{''.join(parts)}
<div class="notes">
<p>Words: {len(doc["tokens"])} unique entries from <code>blissdata_chars.js</code> and <code>blissdata_words.js</code>.
Original drawings are <code>2d/*.svg</code>; 3D equivalents are <code>3d/*.glb</code> (glTF, one unit = one Bliss square)
with a rendered picture <code>3d/*.png</code>. Interactive viewer: <a href="{viewer_href}">3d/viewer.html</a>.</p>
</div>
</main></body></html>
"""
    with open(os.path.join(out, "index.html"), "w", encoding="utf8") as f:
        f.write(page)


def write_3d_page(out, doc, viewer_href):
    """Same poem, showing only the 3D equivalents (index-3d.html)."""
    import html as H
    parts = []
    for stanza in doc["stanzas"]:
        lines = []
        for line in stanza:
            toks = []
            for tok in line:
                rec = doc["tokens"][tok]
                toks.append(
                    '<figure class="w">'
                    f'<a href="{H.escape(rec["glb"])}"><img src="{H.escape(rec["png"])}" alt="{H.escape(tok)}, 3D"></a>'
                    f'<figcaption>{H.escape(tok)}</figcaption></figure>'
                )
            lines.append('<div class="line">' + "".join(toks) + "</div>")
        parts.append('<section class="stanza">' + "".join(lines) + "</section>")
    css = """
:root{--bg:#fbfaf7;--fg:#161616;--mut:#6b6b6b;--line:#e6e2d9;--card:#fff;--acc:#1f5fbf}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--fg);font:17px/1.5 Georgia,"Times New Roman",serif}
main{max-width:980px;margin:0 auto;padding:36px 16px 56px}
h1{font:600 30px/1.2 system-ui,-apple-system,"Helvetica Neue",Arial,sans-serif;margin:0 0 24px}
.stanza{margin:0 0 26px;padding:0 0 0 16px;border-left:2px solid var(--line)}
.line{display:flex;flex-wrap:wrap;align-items:flex-end;gap:10px 14px;margin:0 0 12px}
figure.w{margin:0;width:200px;text-align:center}
figure.w a{display:block;background:var(--card);border:1px solid var(--line);border-radius:12px;padding:8px}
figure.w img{width:100%;height:170px;object-fit:contain;display:block}
figcaption{font:italic 15px/1.3 Georgia,serif;margin-top:4px;color:var(--fg)}
.foot{margin-top:36px;color:var(--mut);font:14px/1.5 system-ui,-apple-system,sans-serif}
.foot a{color:var(--acc)}
@media (max-width:560px){figure.w{width:44%}figure.w img{height:120px}}
"""
    page = (f'<!doctype html><html lang="en"><head><meta charset="utf-8">'
            f'<meta name="viewport" content="width=device-width,initial-scale=1">'
            f'<title>{H.escape(doc["title"])} (3D)</title><style>{css}</style></head><body><main>'
            f'<h1>{H.escape(doc["title"])}</h1>' + "".join(parts) +
            f'<p class="foot">3D equivalents of each word, extruded from its original Blissymbol drawing. '
            f'Click a picture for its .glb model. <a href="{viewer_href}">Interactive 3D viewer</a> &middot; '
            f'<a href="index.html">Original and 3D side by side</a></p></main></body></html>')
    with open(os.path.join(out, "index-3d.html"), "w", encoding="utf8") as f:
        f.write(page)


def main(poem_name="after-rain"):
    spec = POEMS[poem_name]
    TITLE = spec["title"]
    STANZAS = spec["stanzas"]
    chardata, worddata = bc.load_data()
    B = bc.Bliss(chardata, worddata)
    chars = chardata["chars"]
    words = worddata["words"]

    out = os.path.join(REPO, "poem", spec["folder"]) if spec["folder"] else os.path.join(REPO, "poem")
    d2 = os.path.join(out, "2d")
    d3 = os.path.join(out, "3d")
    for d in (d2, d3):
        os.makedirs(d, exist_ok=True)
        for old in glob.glob(os.path.join(d, "*")):
            os.remove(old)

    tokens = {}     # english -> record
    order = []
    lines = []
    for stanza in STANZAS:
        out_stanza = []
        for line in stanza:
            out_line = []
            for tok in line.split():
                if tok in tokens:
                    out_line.append(tok)
                    continue
                key = resolve(tok, chars, words)
                order.append(tok)
                n = len(order)
                base = f"{n:02d}-{slug(tok)}"
                svg = B.svg(key if key in chars else [key], title=tok)
                with open(os.path.join(d2, base + ".svg"), "w", encoding="utf8") as f:
                    f.write(svg)
                mesh = B.mesh(B.geometry(key if key in chars else [key]))
                mesh.export(os.path.join(d3, base + ".glb"), file_type="glb")
                tokens[tok] = {
                    "english": tok,
                    "database_key": key,
                    "kind": "symbol" if key in chars else "word",
                    "svg": f"2d/{base}.svg",
                    "glb": f"3d/{base}.glb",
                    "png": f"3d/{base}.png",
                    "composition": [c for c in words.get(key, [])],
                    "base_symbols": [p["d"] for p in B.expand_word(key if key in chars else [key])["chars"]],
                }
                out_line.append(tok)
            out_stanza.append(out_line)
        lines.append(out_stanza)

    doc = {"title": TITLE, "stanzas": lines, "tokens": tokens}
    with open(os.path.join(out, "poem.json"), "w", encoding="utf8") as f:
        json.dump(doc, f, ensure_ascii=False, indent=1)

    viewer = "../../3d/viewer.html" if spec["folder"] else "../3d/viewer.html"
    write_page(out, doc, viewer)
    write_3d_page(out, doc, viewer)

    print(f"tokens: {len(tokens)} ({sum(1 for t in tokens.values() if t['kind'] == 'word')} words, "
          f"{sum(1 for t in tokens.values() if t['kind'] == 'symbol')} symbols)")
    for tok, rec in tokens.items():
        print(f"  {tok:10s} -> {rec['database_key']!r} ({rec['kind']}, {len(rec['base_symbols'])} symbols)")


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "after-rain")
