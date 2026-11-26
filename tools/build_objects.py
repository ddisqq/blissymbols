"""
Pilot: 3D models of concrete objects, built as solid geometry (not extruded drawings).

Each object is a signed-distance function made from simple solids (boxes, spheres, capsules,
polygons, the implicit heart curve) combined with union, subtraction and smooth blending.
Marching cubes then gives a closed surface, so every model is watertight by construction.

  3d-objects/NNNN-<name>.glb   one model per concrete object (1 unit = 1 Bliss square, base on y=0)

Run from the repository root:  python3 tools/build_objects.py
"""

import glob
import os
import re
import sys

import numpy as np
import shapely
import trimesh
from shapely.geometry import Polygon
from skimage import measure

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import bliss_core as bc  # noqa: E402
import build_solid as bs  # noqa: E402  (decimate)

REPO = bc.REPO
OUT = os.path.join(REPO, "3d-objects")
STEP = 0.015        # grid spacing in units (1 unit = one Bliss square)
MAX_FACES = 6000


# ---------- signed-distance primitives (arrays X, Y, Z; distances in units) ----------

def sd_box(X, Y, Z, c, h, r=0.0):
    qx = np.abs(X - c[0]) - h[0] + r
    qy = np.abs(Y - c[1]) - h[1] + r
    qz = np.abs(Z - c[2]) - h[2] + r
    outside = np.sqrt(np.maximum(qx, 0) ** 2 + np.maximum(qy, 0) ** 2 + np.maximum(qz, 0) ** 2)
    inside = np.minimum(np.maximum(qx, np.maximum(qy, qz)), 0)
    return outside + inside - r


def sd_sphere(X, Y, Z, c, r):
    return np.sqrt((X - c[0]) ** 2 + (Y - c[1]) ** 2 + (Z - c[2]) ** 2) - r


def sd_capsule(X, Y, Z, a, b, r):
    pax, pay, paz = X - a[0], Y - a[1], Z - a[2]
    bax, bay, baz = b[0] - a[0], b[1] - a[1], b[2] - a[2]
    h = np.clip((pax * bax + pay * bay + paz * baz) / (bax * bax + bay * bay + baz * baz), 0, 1)
    dx, dy, dz = pax - bax * h, pay - bay * h, paz - baz * h
    return np.sqrt(dx * dx + dy * dy + dz * dz) - r


def sd_cylinder_y(X, Y, Z, c, radius, half_h):
    d = np.sqrt((X - c[0]) ** 2 + (Z - c[2]) ** 2) - radius
    dy = np.abs(Y - c[1]) - half_h
    return np.minimum(np.maximum(d, dy), 0) + np.sqrt(np.maximum(d, 0) ** 2 + np.maximum(dy, 0) ** 2)


def sd_torus_z(X, Y, Z, c, R, r):
    q = np.sqrt((X - c[0]) ** 2 + (Y - c[1]) ** 2) - R
    return np.sqrt(q * q + (Z - c[2]) ** 2) - r


def smooth_union(a, b, k):
    h = np.clip(0.5 + 0.5 * (b - a) / k, 0, 1)
    return b * (1 - h) + a * h - k * h * (1 - h)


def subtract(a, b):
    return np.maximum(a, -b)


def polygon_sdf_2d(poly, X, Y):
    """Signed distance (units) to the outline of a shapely polygon, for arrays X, Y."""
    shape = X.shape
    pts = shapely.points(X.ravel(), Y.ravel())
    inside = shapely.contains(poly, pts)
    d = shapely.distance(poly.boundary, pts)
    return np.where(inside, -d, d).reshape(shape)


def rounded_extrude(sdf2, Z, half_depth, r):
    """Extrude a 2D signed distance along Z with every edge rounded by r (closed solid)."""
    px = sdf2 + r
    py = np.abs(Z) - half_depth + r
    outer = np.sqrt(np.maximum(px, 0) ** 2 + np.maximum(py, 0) ** 2)
    inner = np.minimum(np.maximum(px, py), 0)
    return outer + inner - r


def heart_sdf_2d(X, Y, cx, cy, s):
    """Implicit heart (x^2+y^2-1)^3 - x^2 y^3 = 0, scaled by s. Approximate distance."""
    x = (X - cx) / s
    y = (Y - cy) / s + 0.1
    g = (x * x + y * y - 1) ** 3 - x * x * y ** 3
    gx = 6 * x * (x * x + y * y - 1) ** 2 - 2 * x * y ** 3
    gy = 6 * y * (x * x + y * y - 1) ** 2 - 3 * x * x * y * y
    return g / (np.sqrt(gx * gx + gy * gy) + 1e-9) * s


def star_polygon(cx, cy, r_out, r_in, points=5, rot=np.pi / 2):
    pts = []
    for i in range(points * 2):
        r = r_out if i % 2 == 0 else r_in
        a = rot + i * np.pi / points
        pts.append((cx + r * np.cos(a), cy + r * np.sin(a)))
    return Polygon(pts)


# ---------- meshing ----------

OFFSETS = (0.37, 0.61, 0.13, 0.83, 0.47)


def polygonise(field_fn, bounds, step=STEP):
    """Sample a signed-distance function and extract a closed, smooth mesh.
    Grid alignment can make a surface non-manifold, so try several offsets until one is closed."""
    for off_frac in OFFSETS:
        mesh = _polygonise_once(field_fn, bounds, step, off_frac)
        if mesh.is_watertight:
            return mesh
    raise ValueError("no closed mesh for any grid offset")


def _polygonise_once(field_fn, bounds, step, off_frac):
    (x0, y0, z0), (x1, y1, z1) = bounds
    # an off-grid offset and a tiny field shift stop coincident faces (e.g. a door resting on the
    # ground) from landing exactly on grid samples, which would make the surface non-manifold
    off = step * off_frac
    xs = np.arange(x0, x1 + step, step) + off
    ys = np.arange(y0, y1 + step, step) + off
    zs = np.arange(z0, z1 + step, step) + off
    X, Y, Z = np.meshgrid(xs, ys, zs, indexing="ij")
    F = field_fn(X, Y, Z) + 1e-4
    if not (F.min() < 0 < F.max()):
        raise ValueError("surface not inside the grid")
    verts, faces, _, _ = measure.marching_cubes(F, level=0.0, spacing=(step, step, step))
    verts = verts + np.array([xs[0], ys[0], zs[0]])
    tri = verts[faces]
    area = np.linalg.norm(np.cross(tri[:, 1] - tri[:, 0], tri[:, 2] - tri[:, 0]), axis=1) / 2
    faces = faces[area > 1e-12]
    mesh = trimesh.Trimesh(vertices=verts, faces=faces[:, ::-1], process=True)
    trimesh.repair.fix_normals(mesh)
    trimesh.smoothing.filter_taubin(mesh, lamb=0.5, nu=-0.53, iterations=6)
    mesh.fix_normals()
    mesh = bs.decimate(mesh, MAX_FACES)
    # place on the ground, centred in x and z
    b = mesh.bounds
    mesh.apply_translation([-(b[0][0] + b[1][0]) / 2, -b[0][1], -(b[0][2] + b[1][2]) / 2])
    return mesh


# ---------- the objects ----------

def house(X, Y, Z):
    body = sd_box(X, Y, Z, (0, 0.36, 0), (0.42, 0.36, 0.36), r=0.02)
    roof_poly = Polygon([(-0.52, 0.66), (0.52, 0.66), (0.0, 1.04)])
    roof = rounded_extrude(polygon_sdf_2d(roof_poly, X, Y), Z, 0.36, 0.03)
    chimney = sd_box(X, Y, Z, (0.26, 0.92, -0.12), (0.06, 0.16, 0.06), r=0.01)
    shape = np.minimum(np.minimum(body, roof), chimney)
    # windows and door carved into the front face
    win_l = sd_box(X, Y, Z, (-0.2, 0.46, 0.36), (0.1, 0.09, 0.08))
    win_r = sd_box(X, Y, Z, (0.2, 0.46, 0.36), (0.1, 0.09, 0.08))
    door = sd_box(X, Y, Z, (0.0, 0.22, 0.36), (0.12, 0.22, 0.08))
    return subtract(subtract(subtract(shape, win_l), win_r), door)


def heart(X, Y, Z):
    d2 = heart_sdf_2d(X, Y, 0.0, 0.46, 0.42)   # heart sits on y = 0
    return rounded_extrude(d2, Z, 0.14, 0.05)


def tree(X, Y, Z):
    trunk = sd_capsule(X, Y, Z, (0, 0.0, 0), (0, 0.55, 0), 0.07)
    crown = sd_sphere(X, Y, Z, (0, 0.74, 0), 0.30)
    crown = smooth_union(crown, sd_sphere(X, Y, Z, (-0.17, 0.6, 0.05), 0.22), 0.12)
    crown = smooth_union(crown, sd_sphere(X, Y, Z, (0.17, 0.62, -0.04), 0.22), 0.12)
    return smooth_union(trunk, crown, 0.08)


def sun(X, Y, Z):
    disc = sd_sphere(X, Y, Z, (0, 0.5, 0), 0.26)
    d = disc
    for i in range(12):
        a = i * 2 * np.pi / 12
        p = (0.5 + 0.0 * 0, 0.5, 0)
        start = (0.36 * np.cos(a), 0.5 + 0.36 * np.sin(a), 0)
        end = (0.5 * np.cos(a), 0.5 + 0.5 * np.sin(a), 0)
        d = np.minimum(d, sd_capsule(X, Y, Z, start, end, 0.035))
    return d


def moon(X, Y, Z):
    full = sd_sphere(X, Y, Z, (0, 0.5, 0), 0.32)
    bite = sd_sphere(X, Y, Z, (0.15, 0.58, 0), 0.28)
    return subtract(full, bite)


def star(X, Y, Z):
    poly = star_polygon(0, 0.5, 0.5, 0.21)
    return rounded_extrude(polygon_sdf_2d(poly, X, Y), Z, 0.1, 0.035)


def window(X, Y, Z):
    frame = sd_box(X, Y, Z, (0, 0.5, 0), (0.42, 0.42, 0.06), r=0.01)
    glass = sd_box(X, Y, Z, (0, 0.5, 0), (0.33, 0.33, 0.1))
    shape = subtract(frame, glass)
    bar_h = sd_box(X, Y, Z, (0, 0.5, 0), (0.33, 0.03, 0.05))
    bar_v = sd_box(X, Y, Z, (0, 0.5, 0), (0.03, 0.33, 0.05))
    return np.minimum(shape, np.minimum(bar_h, bar_v))


def door(X, Y, Z):
    slab = sd_box(X, Y, Z, (0, 0.5, 0), (0.24, 0.5, 0.05), r=0.015)
    panel = sd_box(X, Y, Z, (0, 0.5, 0.05), (0.14, 0.36, 0.02), r=0.01)
    knob = sd_sphere(X, Y, Z, (0.17, 0.48, 0.09), 0.035)
    return np.minimum(smooth_union(slab, panel, 0.01), knob)


def cup(X, Y, Z):
    outer = sd_cylinder_y(X, Y, Z, (0, 0.25, 0), 0.25, 0.25)
    inner = sd_cylinder_y(X, Y, Z, (0, 0.33, 0), 0.21, 0.22)
    body = subtract(outer, inner)
    handle = sd_torus_z(X, Y, Z, (0.25, 0.27, 0), 0.12, 0.035)
    return smooth_union(body, handle, 0.02)


def book(X, Y, Z):
    cover = sd_box(X, Y, Z, (0, 0.4, 0), (0.3, 0.4, 0.07), r=0.025)
    pages = sd_box(X, Y, Z, (0.01, 0.4, 0), (0.27, 0.36, 0.055), r=0.01)
    return subtract(cover, subtract(pages, sd_box(X, Y, Z, (-0.3, 0.4, 0), (0.05, 0.5, 0.2))))


OBJECTS = {
    "house,building,dwelling,residence": (house, (-0.6, 0.0, -0.6), (0.6, 1.15, 0.6)),
    "heart": (heart, (-0.6, -0.05, -0.4), (0.6, 1.05, 0.4)),
    "tree": (tree, (-0.5, -0.05, -0.5), (0.5, 1.15, 0.5)),
    "sun": (sun, (-0.65, 0.0, -0.3), (0.65, 1.1, 0.3)),
    "moon": (moon, (-0.5, 0.1, -0.4), (0.5, 0.95, 0.4)),
    "star": (star, (-0.6, 0.0, -0.2), (0.6, 1.1, 0.2)),
    "window": (window, (-0.5, 0.0, -0.2), (0.5, 1.05, 0.2)),
    "door": (door, (-0.3, 0.0, -0.2), (0.3, 1.05, 0.2)),
    "cup": (cup, (-0.5, 0.0, -0.4), (0.5, 0.55, 0.4)),
    "book": (book, (-0.4, 0.0, -0.2), (0.4, 0.85, 0.2)),
}


def slug(name):
    s = re.sub(r"[^A-Za-z0-9]+", "-", name.split(",")[0]).strip("-").lower()
    return s or "object"


def main():
    chardata, worddata = bc.load_data()
    os.makedirs(OUT, exist_ok=True)
    for old in glob.glob(os.path.join(OUT, "*.glb")):
        os.remove(old)
    index = {}
    import csv
    with open(os.path.join(REPO, "dictionary", "symbols_index.csv"), encoding="utf8") as f:
        for row in csv.DictReader(f):
            index[row["database_key"]] = row["id"]

    for key, (fn, lo, hi) in OBJECTS.items():
        if key not in index:
            name = f"w-{slug(key)}.glb"  # a word in the database rather than a symbol
        else:
            name = f"{index[key]}-{slug(key)}.glb"
        pad = 0.12
        bounds = ((lo[0] - pad, lo[1] - pad, lo[2] - pad), (hi[0] + pad, hi[1] + pad, hi[2] + pad))
        mesh = polygonise(fn, bounds)
        mesh.export(os.path.join(OUT, name), file_type="glb")
        print(f"{name}: faces {len(mesh.faces)}  watertight {mesh.is_watertight}  "
              f"size {[round(float(v), 2) for v in mesh.extents]}")


if __name__ == "__main__":
    main()
