"""
Python port of blissviewer.ts (the reference Blissymbol renderer in this repo).

It resolves Blissymbol ids (characters, indicators, words) into primitive
drawing elements exactly the way blissviewer.ts does, and from those it can
produce:

  * standalone SVG (same geometry as the browser viewer, same CSS values),
  * 2D shapely geometry (strokes turned into filled outlines),
  * 3D triangle meshes (the 2D geometry extruded to a solid slab).

Coordinate conventions (copied from blissviewer.ts):
  * Data coordinates have the origin at the bottom of a character, y pointing
    up. The viewer flips them with  svg_y = BLISSHEIGHT - data_y  (BLISSHEIGHT = 320).
  * Stroke width is 8 with round caps and joins (blissviewer.css).
"""

import math
import os

import numpy as np
import shapely
from shapely import make_valid
from shapely.geometry import LineString, Point, Polygon, MultiPolygon, GeometryCollection
from shapely.ops import unary_union
from matplotlib.font_manager import FontProperties
from matplotlib.textpath import TextPath, TextToPath

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

BLISSHEIGHT = 320.0
BLISSQUARE = 128.0
BLISSQSPACE = BLISSQUARE / 4
MARGIN = 8.0          # viewer default margin
RADIUS = 4.0          # dot radius used by blissdemo.js / README
STROKE = 8.0          # blissviewer.css stroke-width
FONT_FILE = "/usr/share/fonts/truetype/liberation/LiberationSans-Regular.ttf"  # Helvetica/Arial metrics
FONT_SIZE = 88        # font-size used for "text" paths in the data
MESH_UNIT = 128.0     # 1 Bliss square = 1 glTF unit
MESH_DEPTH = 40.0     # extrusion depth in data units (five stroke widths, so the sides read as solid)

MODIFIERS = {
    'a,an,any', 'ago,then_(past)', 'belongs_to,of_(possessive)', 'bliss-name',
    'comparative_more', 'dot', 'generalization', 'group_of,much_of,many_of,quantity_of',
    'combine_marker', 'intensity', 'line,stripe', 'metaphor', 'minus,no,without', 'more',
    'most,maximum', 'now', 'opposite_meaning,opposite_of,opposite',
    'part,bit,piece,portion,part_of', 'superlative_most', 'then,so,later',
}
PUNCTUATIONS = {'comma', 'period,point,full_stop,decimal_point', 'question_mark', 'exclamation_mark'}


def load_data(repo=REPO):
    """Load the two database files. They are valid Python too (see README)."""
    ns = {}
    for name in ("blissdata_chars.js", "blissdata_words.js"):
        with open(os.path.join(repo, name), encoding="utf8") as f:
            exec(f.read(), ns)
    return ns["BLISS_CHAR_DATA"], ns["BLISS_WORD_DATA"]


def fmt(v):
    s = f"{float(v):.3f}".rstrip("0").rstrip(".")
    return "0" if s in ("-0", "") else s


def xml_escape(s):
    return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;").replace('"', "&quot;")


class Bliss:
    def __init__(self, chardata, worddata, radius=RADIUS, margin=MARGIN):
        self.cd = chardata
        self.wd = worddata
        self.chars = chardata["chars"]
        self.center = chardata["center"]
        self.kern_l = chardata["kerning_left"]
        self.kern_r = chardata["kerning_right"]
        self.paths = chardata["paths"]
        self.shapes = chardata["shapes"]
        self.words = worddata["words"]
        self.radius = radius
        self.margin = margin

    # ----- predicates (blissviewer.ts "Private predicates") -----

    @staticmethod
    def is_modifier(m):
        return m in MODIFIERS

    @staticmethod
    def is_digit(d):
        return d[-7:] == "(digit)"

    @staticmethod
    def is_letter(l):
        return l[-11:] in ("(uppercase)", "(lowercase)")

    @staticmethod
    def is_punctuation(p):
        return p in PUNCTUATIONS

    def is_indicator(self, ind):
        return ind[:10] == "indicator_" and not self.is_modifier(ind)

    # ----- lookup -----

    def get_data(self, id_):
        for src in (self.paths, self.shapes, self.chars, self.words):
            if id_ in src:
                return src[id_]
        raise KeyError(id_)

    # ----- word expansion (expand_word / expand_list / spacing / kerning) -----

    def _default_kerning(self, h):
        if not h:
            return 12
        if h <= 80:
            return 2
        if h <= 144:
            return 6
        return 14

    def _kerning_possible(self, prev, cur):
        if self.chars[prev].get("w", 0) <= 24 or self.chars[cur].get("w", 0) <= 24:
            return False
        right = self.kern_r.get(prev) or self._default_kerning(self.chars[prev].get("h"))
        left = self.kern_l.get(cur) or self._default_kerning(self.chars[cur].get("h"))
        return (right & left) == 0

    def _spacing(self, prev, cur):
        if prev is None:
            return 0
        if self._kerning_possible(prev, cur):
            return 0
        if self.is_digit(prev) and self.is_digit(cur):
            return BLISSQSPACE / 2
        if self.is_letter(prev) and self.is_letter(cur):
            return BLISSQSPACE / 2
        if cur == "comma":
            return BLISSQSPACE * 3 / 4
        return BLISSQSPACE

    def _expand_list(self, words, inds):
        chars = []
        for n, w in enumerate(words):
            if self.is_indicator(w) and chars:
                chars[-1]["inds"].extend(inds)
                chars[-1]["inds"].append(w)
                inds = []
            elif self.is_modifier(w) or self.is_punctuation(w) or (n == 0 and self.is_digit(w)):
                chars.append({"ch": w, "inds": []})
            else:
                chars.append({"ch": w, "inds": inds})
                inds = []
        groups = []
        new_inds = []
        for c in chars:
            ch, cinds = c["ch"], c["inds"]
            if ch in self.words:
                sub_groups, sub_inds = self._expand_list(self.words[ch], new_inds + cinds)
                groups.extend(sub_groups)
                new_inds = sub_inds
            else:
                if ch not in self.chars:
                    print("Unknown character:", ch)
                    ch = "question_mark"
                groups.append({"ch": ch, "inds": new_inds + cinds})
                new_inds = []
        return groups, new_inds + inds

    def expand_word(self, word):
        """Lay out a Blissword (list of ids) into positioned characters."""
        if isinstance(word, str):
            word = [word]
        groups, leftover = self._expand_list(list(word), [])
        if leftover:
            print("Indicators left over:", word, leftover)
        chars = []
        x, left, right, prev = 0.0, 0.0, 0.0, None
        for g in groups:
            ch, inds = g["ch"], g["inds"]
            w = self.chars[ch].get("w", 0)
            x += self._spacing(prev, ch)
            chars.append({"x": x, "y": 0, "d": ch})
            if inds:
                iw = (len(inds) - 1) * BLISSQSPACE / 2
                for ind in inds:
                    iw += self.chars[ind].get("w", 0)
                    if ind in self.center:
                        iw += 2 * self.center[ind]
                ix = x + (w - iw) / 2
                if ch in self.center:
                    ix += self.center[ch]
                left = min(left, ix)
                iy = max(0, self.chars[ch].get("h", 0) - 192)
                for i, ind in enumerate(inds):
                    if i > 0:
                        ix += BLISSQSPACE / 2
                    chars.append({"x": ix, "y": iy, "d": ind})
                    ix += self.chars[ind].get("w", 0)
                right = max(right, ix)
            x += w
            prev = ch
        right = max(right, x)
        return {"top": 0.0, "bottom": BLISSHEIGHT, "left": left, "right": right, "chars": chars}

    # ----- primitives (to_svg_obj, but returning data instead of strings) -----

    def primitives(self, obj, x=0.0, y=0.0, out=None):
        if out is None:
            out = []
        if isinstance(obj, str):
            self.primitives(self.get_data(obj), x, y, out)
        elif isinstance(obj, list):
            for o in obj:
                self.primitives(o, x, y, out)
        elif "d" in obj:
            x += obj.get("x", 0)
            y += obj.get("y", 0)
            self.primitives(obj["d"], x, y, out)
        else:
            clone = {}
            for k, v in obj.items():
                if k[0] == "x" or k == "qx":
                    clone[k] = v + x
                elif k[0] == "y" or k == "qy":
                    clone[k] = BLISSHEIGHT - v - y
                else:
                    clone[k] = v
            if clone["form"] == "text":
                clone["x"] += clone["w"] / 2
                clone["y"] += clone["h"]
            elif clone["form"] == "dot":
                clone["r"] = self.radius
            out.append(clone)
        return out

    # ----- SVG output -----

    def svg_element(self, p):
        f = p["form"]
        if f == "dot":
            return f'<circle class="bliss-dot" cx="{fmt(p["x"])}" cy="{fmt(p["y"])}" r="{fmt(p["r"])}"/>'
        if f == "disc":
            return f'<circle class="bliss-disc" cx="{fmt(p["x"])}" cy="{fmt(p["y"])}" r="{fmt(p["r"])}"/>'
        if f == "circle":
            return f'<circle class="bliss-line" cx="{fmt(p["x"])}" cy="{fmt(p["y"])}" r="{fmt(p["r"])}"/>'
        if f == "text":
            return (f'<text class="bliss-text" text-anchor="middle" x="{fmt(p["x"])}" y="{fmt(p["y"])}" '
                    f'style="font-size:{fmt(p["fontsize"])}px">{xml_escape(p["text"])}</text>')
        if f == "line":
            return (f'<line class="bliss-line" x1="{fmt(p["x1"])}" y1="{fmt(p["y1"])}" '
                    f'x2="{fmt(p["x2"])}" y2="{fmt(p["y2"])}"/>')
        if f == "arc":
            return (f'<path class="bliss-line" d="M {fmt(p["x1"])},{fmt(p["y1"])} '
                    f'A {fmt(p["rx"])},{fmt(p["ry"])} 0 0,0 {fmt(p["x2"])},{fmt(p["y2"])}"/>')
        if f == "bigarc":
            return (f'<path class="bliss-line" d="M {fmt(p["x1"])},{fmt(p["y1"])} '
                    f'A {fmt(p["rx"])},{fmt(p["ry"])} 0 1,0 {fmt(p["x2"])},{fmt(p["y2"])}"/>')
        if f == "quadratic":
            return (f'<path class="bliss-line" d="M {fmt(p["x1"])},{fmt(p["y1"])} '
                    f'Q {fmt(p["qx"])},{fmt(p["qy"])} {fmt(p["x2"])},{fmt(p["y2"])}"/>')
        raise ValueError(f)

    SVG_STYLE = (
        ".bliss-line,.bliss-disc,.bliss-dot{stroke:#000;stroke-width:8;stroke-linejoin:round;stroke-linecap:round}"
        ".bliss-line{fill:none}.bliss-disc,.bliss-dot{fill:#000}"
        ".bliss-text{font-family:'Helvetica Neue',Helvetica,Arial,'Liberation Sans',sans-serif}"
    )

    def svg(self, word, title=None):
        """Standalone SVG for a Blissword, same viewBox/margins as add_blissvg()."""
        exp = self.expand_word(word)
        m = self.margin
        x0, y0 = exp["left"] - m, exp["top"] - m
        w = exp["right"] - exp["left"] + 2 * m
        h = exp["bottom"] - exp["top"] + 2 * m
        body = "".join(self.svg_element(p) for p in self.primitives(exp["chars"]))
        t = f"<title>{xml_escape(title)}</title>" if title else ""
        return (f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="{fmt(x0)} {fmt(y0)} {fmt(w)} {fmt(h)}" '
                f'width="{fmt(w)}" height="{fmt(h)}">{t}<style>{self.SVG_STYLE}</style>'
                f'<g>{body}</g></svg>\n')

    # ----- 2D geometry (SVG frame, y pointing down) -----

    @staticmethod
    def _svg_arc_points(x1, y1, x2, y2, rx, ry, large, sweep=0, steps=None):
        """Sample an SVG elliptical arc (endpoint parameterisation, SVG spec F.6.5)."""
        rx, ry = abs(rx), abs(ry)
        dx2, dy2 = (x1 - x2) / 2.0, (y1 - y2) / 2.0
        lam = dx2 * dx2 / (rx * rx) + dy2 * dy2 / (ry * ry)
        if lam > 1:
            rx *= math.sqrt(lam)
            ry *= math.sqrt(lam)
        num = rx * rx * ry * ry - rx * rx * dy2 * dy2 - ry * ry * dx2 * dx2
        den = rx * rx * dy2 * dy2 + ry * ry * dx2 * dx2
        coef = math.sqrt(max(0.0, num / den)) if den else 0.0
        if large == sweep:
            coef = -coef
        cxp = coef * rx * dy2 / ry
        cyp = -coef * ry * dx2 / rx
        cx = cxp + (x1 + x2) / 2.0
        cy = cyp + (y1 + y2) / 2.0

        def ang(ux, uy, vx, vy):
            a = math.atan2(ux * vy - uy * vx, ux * vx + uy * vy)
            return a

        ux, uy = (dx2 - cxp) / rx, (dy2 - cyp) / ry
        vx, vy = (-dx2 - cxp) / rx, (-dy2 - cyp) / ry
        theta1 = ang(1.0, 0.0, ux, uy)
        dtheta = ang(ux, uy, vx, vy)
        if not sweep and dtheta > 0:
            dtheta -= 2 * math.pi
        if sweep and dtheta < 0:
            dtheta += 2 * math.pi
        if steps is None:
            steps = max(8, int(abs(dtheta) * max(rx, ry) / 2))
        ts = np.linspace(theta1, theta1 + dtheta, steps + 1)
        return [(cx + rx * math.cos(t) - 0.0, cy + ry * math.sin(t)) for t in ts]

    def _prim_geom(self, p):
        f = p["form"]
        half = STROKE / 2
        if f in ("dot", "disc"):
            return Point(p["x"], p["y"]).buffer(p["r"] + half, quad_segs=8)
        if f == "circle":
            c = Point(p["x"], p["y"])
            r = p["r"]
            if r - half <= 0:
                return c.buffer(r + half, quad_segs=8)
            return c.buffer(r + half, quad_segs=8).difference(c.buffer(r - half, quad_segs=8))
        if f == "line":
            return LineString([(p["x1"], p["y1"]), (p["x2"], p["y2"])]).buffer(
                half, cap_style="round", join_style="round", quad_segs=8)
        if f in ("arc", "bigarc"):
            pts = self._svg_arc_points(p["x1"], p["y1"], p["x2"], p["y2"], p["rx"], p["ry"],
                                       large=1 if f == "bigarc" else 0, sweep=0)
            return LineString(pts).buffer(half, cap_style="round", join_style="round", quad_segs=8)
        if f == "quadratic":
            P0 = np.array([p["x1"], p["y1"]])
            P1 = np.array([p["qx"], p["qy"]])
            P2 = np.array([p["x2"], p["y2"]])
            ts = np.linspace(0, 1, 64)[:, None]
            pts = (1 - ts) ** 2 * P0 + 2 * (1 - ts) * ts * P1 + ts ** 2 * P2
            return LineString(pts).buffer(half, cap_style="round", join_style="round", quad_segs=8)
        if f == "text":
            return self._text_geom(p)
        raise ValueError(f)

    def _text_geom(self, p):
        fp = FontProperties(fname=FONT_FILE, size=FONT_SIZE)
        text = p["text"]
        width = TextToPath().get_text_width_height_descent(text, fp, ismath=False)[0]
        tp = TextPath((0, 0), text, size=FONT_SIZE, prop=fp)
        geom = Polygon()
        for ring in tp.to_polygons(closed_only=True):
            if len(ring) < 3:
                continue
            # even-odd fill so that counters (holes) in glyphs such as "o" or "A" stay empty
            geom = geom.symmetric_difference(Polygon(ring).buffer(0))
        ax = p["x"] - width / 2.0
        ay = p["y"]
        return shapely.transform(geom, lambda c: np.column_stack([c[:, 0] + ax, ay - c[:, 1]]))

    def geometry(self, word):
        """Union of all strokes/fills of a Blissword, in SVG frame."""
        exp = self.expand_word(word)
        parts = [self._prim_geom(p) for p in self.primitives(exp["chars"])]
        return make_valid(unary_union(parts)).buffer(0)

    # ----- 3D -----

    def mesh(self, geom, depth=MESH_DEPTH, unit=MESH_UNIT):
        """Extrude a 2D SVG-frame geometry into a solid (trimesh), in glTF axes (Y up, Z = depth)."""
        import trimesh
        from trimesh.creation import extrude_polygon

        if geom.is_empty:
            raise ValueError("empty geometry")
        # SVG y-down -> Y-up, scaled so one Bliss square = one unit
        g = shapely.transform(geom, lambda c: np.column_stack([c[:, 0] / unit, (BLISSHEIGHT - c[:, 1]) / unit]))
        g = g.simplify(0.4 / unit, preserve_topology=True)
        polys = list(g.geoms) if isinstance(g, (MultiPolygon, GeometryCollection)) else [g]
        meshes = []
        for poly in polys:
            if not isinstance(poly, Polygon) or poly.is_empty or poly.area <= 0:
                continue
            m = extrude_polygon(poly, height=depth / unit)
            meshes.append(m)
        mesh = trimesh.util.concatenate(meshes)
        mesh.fix_normals()
        # centre in X/Y on the origin, keep Z from 0 to depth
        b = mesh.bounds
        mesh.apply_translation([-(b[0][0] + b[1][0]) / 2, -(b[0][1] + b[1][1]) / 2, 0])
        return mesh
