"""
Build the supporting files for every Blissymbol character in the database:

  svg/NNNN-<name>.svg   original 2D drawing (standalone SVG, same geometry as blissviewer.js)
  3d/NNNN-<name>.glb    3D equivalent: the same drawing extruded into a solid
  dictionary/symbols_index.csv   one row per symbol, with names, sizes and usage counts

Run from anywhere:  python3 tools/build_symbols.py
"""

import csv
import glob
import os
import re
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import bliss_core as bc  # noqa: E402

REPO = bc.REPO


def slug(name):
    base = name.split(",")[0]
    s = re.sub(r"[^A-Za-z0-9]+", "-", base).strip("-").lower()
    return s or "symbol"


def main():
    chardata, worddata = bc.load_data()
    B = bc.Bliss(chardata, worddata)
    names = list(chardata["chars"].keys())

    svg_dir = os.path.join(REPO, "svg")
    glb_dir = os.path.join(REPO, "3d")
    dic_dir = os.path.join(REPO, "dictionary")
    for d in (svg_dir, glb_dir, dic_dir):
        os.makedirs(d, exist_ok=True)
        for old in glob.glob(os.path.join(d, "*")):
            if os.path.isfile(old) and old.endswith((".svg", ".glb", ".csv")):
                os.remove(old)

    # --- usage counts: how many dictionary headwords use each symbol (directly or inside a sub-word) ---
    usage = {n: 0 for n in names}
    for head in worddata["words"]:
        seen = {p["d"] for p in B.expand_word([head])["chars"]}
        for s in seen:
            if s in usage:
                usage[s] += 1

    rows = []
    t0 = time.time()
    failures = []
    for i, name in enumerate(names, start=1):
        stem = f"{i:04d}-{slug(name)}"
        svg_name = f"{stem}.svg"
        glb_name = f"{stem}.glb"
        svg_text = B.svg([name], title=name.replace("_", " "))
        with open(os.path.join(svg_dir, svg_name), "w", encoding="utf8") as f:
            f.write(svg_text)

        n_prims = len(B.primitives(chardata["chars"][name]))
        watertight = ""
        try:
            geom = B.geometry([name])
            mesh = B.mesh(geom)
            mesh.export(os.path.join(glb_dir, glb_name), file_type="glb")
            watertight = str(bool(mesh.is_watertight))
            bounds = mesh.extents
            tri = len(mesh.faces)
            size_x, size_y, size_z = (round(float(v), 3) for v in bounds)
        except Exception as exc:  # keep going, but record the failure
            failures.append((name, repr(exc)))
            tri, size_x, size_y, size_z = 0, "", "", ""
            glb_name = ""

        c = chardata["chars"][name]
        rows.append({
            "id": f"{i:04d}",
            "primary_name": name.split(",")[0],
            "all_names": " | ".join(name.split(",")),
            "database_key": name,
            "width_units": c.get("w", ""),
            "height_units": c.get("h", ""),
            "drawing_parts": n_prims,
            "used_in_headwords": usage[name],
            "svg": f"svg/{svg_name}",
            "glb_3d": f"3d/{glb_name}" if glb_name else "",
            "mesh_triangles": tri,
            "mesh_extent_x": size_x,
            "mesh_extent_y": size_y,
            "mesh_extent_z": size_z,
            "mesh_watertight": watertight,
        })
        if i % 200 == 0:
            print(f"  {i}/{len(names)} symbols ({time.time() - t0:.0f}s)", flush=True)

    with open(os.path.join(dic_dir, "symbols_index.csv"), "w", encoding="utf8", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)

    print(f"symbols: {len(rows)}  svg: {len(rows)}  glb: {sum(1 for r in rows if r['glb_3d'])}  "
          f"time: {time.time() - t0:.0f}s")
    print("watertight:", sum(1 for r in rows if r["mesh_watertight"] == "True"), "of", len(rows))
    if failures:
        print("FAILURES:", failures)


if __name__ == "__main__":
    main()
