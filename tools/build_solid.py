"""
Build a second 3D set: closed, fully enclosed solids with rounded edges.

Each symbol is turned into a signed-distance field, then a closed surface is extracted with
marching cubes. The result is watertight by construction, and every edge is rounded like a
real moulded object (radius = half a stroke, so the strokes read as solid bars).

  3d-solid/NNNN-<name>.glb    closed solid for each symbol (glTF, 1 Bliss square = 1 unit)

Run:  python3 tools/build_solid.py
"""

import glob
import os
import re
import sys
import time

import numpy as np
import shapely
import trimesh
from scipy import ndimage
from skimage import measure

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import bliss_core as bc  # noqa: E402

REPO = bc.REPO
OUT = os.path.join(REPO, "3d-solid")

STEP = 2.0          # sample spacing in Bliss data units
HALF_DEPTH = 20.0   # the solid is 40 units thick (five stroke widths)
EDGE_R = 4.0        # rounding radius of every edge = half a stroke
MARGIN = 6.0        # empty space around the drawing, in units
SMOOTH_ITERS = 12   # Taubin smoothing passes (volume-preserving, keeps the surface closed)
MAX_FACES = 4000    # larger solids are decimated (topology and volume are preserved; checked)


def slug(name):
    s = re.sub(r"[^A-Za-z0-9]+", "-", name.split(",")[0]).strip("-").lower()
    return s or "symbol"


def signed_distance_2d(geom, step):
    """Signed distance (units) to the outline of a shapely geometry in SVG frame.
    Negative inside, positive outside. Returns (sdf, x0, y0)."""
    minx, miny, maxx, maxy = geom.bounds
    x0, y0 = minx - MARGIN, miny - MARGIN
    nx = int(np.ceil((maxx - minx + 2 * MARGIN) / step)) + 1
    ny = int(np.ceil((maxy - miny + 2 * MARGIN) / step)) + 1
    xs = x0 + np.arange(nx) * step
    ys = y0 + np.arange(ny) * step
    X, Y = np.meshgrid(xs, ys, indexing="xy")          # shape (ny, nx)
    inside = shapely.contains_xy(geom, X.ravel(), Y.ravel()).reshape(X.shape)
    # distance to the nearest outline point, measured in grid steps
    d_out = ndimage.distance_transform_edt(~inside)     # for outside pixels
    d_in = ndimage.distance_transform_edt(inside)       # for inside pixels
    sdf = (d_out - d_in) * step
    return sdf, x0, y0


def decimate(mesh, max_faces=MAX_FACES):
    """Quadric edge-collapse down to max_faces, keeping boundaries and topology.
    Returns the original mesh if the result is not closed or the volume changes."""
    if len(mesh.faces) <= max_faces:
        return mesh
    import pymeshlab
    ms = pymeshlab.MeshSet()
    ms.add_mesh(pymeshlab.Mesh(vertex_matrix=mesh.vertices.astype(np.float64),
                               face_matrix=mesh.faces.astype(np.int32)))
    ms.apply_filter("meshing_decimation_quadric_edge_collapse", targetfacenum=max_faces,
                    preserveboundary=True, preservenormal=True, preservetopology=True,
                    optimalplacement=True, qualitythr=0.5)
    d = ms.current_mesh()
    out = trimesh.Trimesh(vertices=d.vertex_matrix(), faces=d.face_matrix(), process=True)
    trimesh.repair.fix_normals(out)
    if not out.is_watertight or abs(out.volume - mesh.volume) > 0.02 * abs(mesh.volume):
        return mesh
    return out


def build_solid(geom):
    sdf2, x0, y0 = signed_distance_2d(geom, STEP)
    ny, nx = sdf2.shape
    zmax = HALF_DEPTH + EDGE_R + 2 * STEP
    zs = np.arange(-zmax, zmax + STEP / 2, STEP)
    # rounded extrusion of a 2D distance field (inigo quilez "opExtrusion" with rounding):
    # shrink by the rounding radius, extrude to +/-HALF_DEPTH, then grow the surface back out
    px = sdf2[None, :, :] + EDGE_R                       # (1, ny, nx)
    py = np.abs(zs)[:, None, None] - HALF_DEPTH + EDGE_R  # (nz, 1, 1)
    outer = np.sqrt(np.maximum(px, 0) ** 2 + np.maximum(py, 0) ** 2)
    inner = np.minimum(np.maximum(px, py), 0)
    field = outer + inner - EDGE_R                       # (nz, ny, nx)

    verts, faces, _, _ = measure.marching_cubes(field, level=0.0, spacing=(STEP, STEP, STEP))
    # verts columns: (z, y, x) in grid units * STEP, relative to the grid origin
    z = verts[:, 0] - zmax
    y = verts[:, 1] + y0
    x = verts[:, 2] + x0
    # SVG frame (y down) -> Y up, centred, scaled so one Bliss square = one unit
    X = x / bc.MESH_UNIT
    Y = (bc.BLISSHEIGHT - y) / bc.MESH_UNIT
    Z = z / bc.MESH_UNIT
    v = np.column_stack([X, Y, Z])
    v[:, 0] -= (v[:, 0].min() + v[:, 0].max()) / 2
    v[:, 1] -= (v[:, 1].min() + v[:, 1].max()) / 2
    # marching cubes emits zero-area triangles where the surface passes exactly through grid
    # points; they make edges non-manifold, so drop them
    tri = v[faces]
    area = np.linalg.norm(np.cross(tri[:, 1] - tri[:, 0], tri[:, 2] - tri[:, 0]), axis=1) / 2
    faces = faces[area > 1e-9]
    mesh = trimesh.Trimesh(vertices=v, faces=faces[:, ::-1], process=True)
    trimesh.repair.fix_normals(mesh)
    if SMOOTH_ITERS:
        trimesh.smoothing.filter_taubin(mesh, lamb=0.5, nu=-0.53, iterations=SMOOTH_ITERS)
        mesh.fix_normals()
    return decimate(mesh)


def main():
    chardata, worddata = bc.load_data()
    B = bc.Bliss(chardata, worddata)
    names = list(chardata["chars"].keys())
    os.makedirs(OUT, exist_ok=True)
    for old in glob.glob(os.path.join(OUT, "*.glb")):
        os.remove(old)

    t0 = time.time()
    closed = 0
    fails = []
    for i, name in enumerate(names, start=1):
        stem = f"{i:04d}-{slug(name)}"
        try:
            mesh = build_solid(B.geometry([name]))
            if mesh.is_watertight:
                closed += 1
            mesh.export(os.path.join(OUT, stem + ".glb"), file_type="glb")
        except Exception as exc:
            fails.append((name, repr(exc)))
        if i % 200 == 0:
            print(f"  {i}/{len(names)} ({time.time() - t0:.0f}s)", flush=True)

    print(f"solids: {len(names)}  watertight: {closed}  time: {time.time() - t0:.0f}s")
    if fails:
        print("FAILURES:", fails[:10])


if __name__ == "__main__":
    main()
