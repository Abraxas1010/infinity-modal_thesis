#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np


def load_points(path: Path) -> np.ndarray:
    pts = json.loads(path.read_text())
    arr = np.array([[p["x"], p["y"], p["z"]] for p in pts], dtype=float)
    if arr.ndim != 2 or arr.shape[1] != 3:
        raise ValueError(f"Expected Nx3 points, got {arr.shape}")
    return arr


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--in", dest="inp", required=True, help="Input JSON array from modal_thesis_spiral_dump")
    ap.add_argument("--out-dir", required=True, help="Output directory for PNGs")
    ap.add_argument("--title", default="Spiral g(k) in R^3", help="Plot title")
    args = ap.parse_args()

    inp = Path(args.inp)
    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    pts = load_points(inp)
    x, y, z = pts[:, 0], pts[:, 1], pts[:, 2]

    # 2D projection (xy)
    plt.figure(figsize=(6, 6), dpi=160)
    plt.plot(x, y, "-o", linewidth=1.0, markersize=2.5)
    plt.gca().set_aspect("equal", adjustable="box")
    plt.title("Spiral g(k): XY projection (unit circle)")
    plt.xlabel("x")
    plt.ylabel("y")
    plt.grid(True, linewidth=0.3, alpha=0.6)
    plt.tight_layout()
    plt.savefig(out_dir / "spiral_g_xy.png")
    plt.close()

    # 3D plot
    fig = plt.figure(figsize=(7, 5), dpi=160)
    ax = fig.add_subplot(111, projection="3d")
    ax.plot(x, y, z, "-o", linewidth=1.0, markersize=2.0)
    ax.set_title(args.title)
    ax.set_xlabel("x")
    ax.set_ylabel("y")
    ax.set_zlabel("z (iteration level / pitch·t)")
    # Make aspect less distorted (best effort).
    max_range = max(x.max() - x.min(), y.max() - y.min(), z.max() - z.min())
    mid_x = 0.5 * (x.max() + x.min())
    mid_y = 0.5 * (y.max() + y.min())
    mid_z = 0.5 * (z.max() + z.min())
    ax.set_xlim(mid_x - max_range / 2, mid_x + max_range / 2)
    ax.set_ylim(mid_y - max_range / 2, mid_y + max_range / 2)
    ax.set_zlim(mid_z - max_range / 2, mid_z + max_range / 2)
    plt.tight_layout()
    plt.savefig(out_dir / "spiral_g_3d.png")
    plt.close()

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
