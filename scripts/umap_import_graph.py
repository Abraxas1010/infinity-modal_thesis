#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np
import umap


IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)\s*$")


@dataclass(frozen=True)
class Module:
    name: str
    path: Path
    imports: list[str]


def lean_module_name(root: Path, file_path: Path) -> str:
    rel = file_path.relative_to(root)
    if rel.suffix != ".lean":
        raise ValueError(f"Expected .lean: {file_path}")
    return ".".join(rel.with_suffix("").parts)


def parse_imports(path: Path) -> list[str]:
    out: list[str] = []
    for line in path.read_text().splitlines():
        m = IMPORT_RE.match(line)
        if m:
            out.append(m.group(1))
    return out


def collect_modules(src_dir: Path) -> list[Module]:
    modules: list[Module] = []
    for p in sorted(src_dir.rglob("*.lean")):
        name = lean_module_name(src_dir, p)
        modules.append(Module(name=name, path=p, imports=parse_imports(p)))
    return modules


def build_feature_matrix(mods: list[Module]) -> tuple[np.ndarray, list[str]]:
    names = [m.name for m in mods]
    name_to_idx = {n: i for i, n in enumerate(names)}
    X = np.zeros((len(mods), len(mods)), dtype=np.float32)
    for i, m in enumerate(mods):
        for imp in m.imports:
            j = name_to_idx.get(imp)
            if j is not None:
                X[i, j] = 1.0
    return X, names


def plot_embedding(names: list[str], emb: np.ndarray, out_path: Path, title: str) -> None:
    out_path.parent.mkdir(parents=True, exist_ok=True)
    if emb.shape[1] == 2:
        plt.figure(figsize=(8, 6), dpi=160)
        plt.scatter(emb[:, 0], emb[:, 1], s=20)
        for i, name in enumerate(names):
            plt.annotate(name.split(".")[-1], (emb[i, 0], emb[i, 1]), fontsize=7, alpha=0.85)
        plt.title(title)
        plt.tight_layout()
        plt.savefig(out_path)
        plt.close()
    else:
        # Save a simple JSON for 3D consumers (and future interactive viz).
        pts = [{"name": names[i], "x": float(emb[i, 0]), "y": float(emb[i, 1]), "z": float(emb[i, 2])} for i in range(len(names))]
        out_path.write_text(json.dumps(pts, indent=2))


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--src", default="lean/ModalThesis", help="Lean sources root (module tree)")
    ap.add_argument("--out-dir", default="docs", help="Output directory")
    ap.add_argument("--seed", type=int, default=0)
    args = ap.parse_args()

    src = Path(args.src)
    out_dir = Path(args.out_dir)

    mods = collect_modules(src)
    X, names = build_feature_matrix(mods)

    reducer2 = umap.UMAP(n_components=2, random_state=args.seed, metric="cosine")
    emb2 = reducer2.fit_transform(X)
    plot_embedding(names, emb2, out_dir / "umap_imports_2d.png", "UMAP (2D) of local import graph (one-hot imports)")

    reducer3 = umap.UMAP(n_components=3, random_state=args.seed, metric="cosine")
    emb3 = reducer3.fit_transform(X)
    plot_embedding(names, emb3, out_dir / "umap_imports_3d.json", "UMAP (3D) of local import graph")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
