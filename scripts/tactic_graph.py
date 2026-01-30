#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
from collections import Counter, defaultdict
from pathlib import Path

import matplotlib.pyplot as plt
import networkx as nx


TACTIC_TOKENS = [
    "simp",
    "simp_all",
    "linarith",
    "nlinarith",
    "ring",
    "aesop",
    "omega",
    "decide",
    "cases",
    "by_cases",
    "induction",
    "intro",
    "refine",
    "exact",
    "apply",
]

TACTIC_RE = re.compile(r"\\b(" + "|".join(re.escape(t) for t in TACTIC_TOKENS) + r")\\b")


def extract_tactics_from_file(path: Path) -> list[str]:
    txt = path.read_text()
    return TACTIC_RE.findall(txt)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--src", default="lean/ModalThesis", help="Scan Lean sources under this dir")
    ap.add_argument("--out-dir", default="docs", help="Output directory")
    ap.add_argument("--top", type=int, default=20, help="Keep top-k tactics by count")
    args = ap.parse_args()

    src = Path(args.src)
    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    per_file: dict[Path, list[str]] = {}
    counts = Counter()
    for p in sorted(src.rglob("*.lean")):
        toks = extract_tactics_from_file(p)
        per_file[p] = toks
        counts.update(toks)

    keep = {t for t, _c in counts.most_common(args.top)}

    G = nx.Graph()
    for t in keep:
        G.add_node(t, count=int(counts[t]))

    # Co-occurrence by file (minimal but robust and reproducible).
    for p, toks in per_file.items():
        toks = [t for t in toks if t in keep]
        uniq = sorted(set(toks))
        for i in range(len(uniq)):
            for j in range(i + 1, len(uniq)):
                a, b = uniq[i], uniq[j]
                G.add_edge(a, b, weight=G.get_edge_data(a, b, {}).get("weight", 0) + 1)

    # Save JSON (for interactive consumers).
    nodes = [{"id": n, "count": int(G.nodes[n]["count"])} for n in G.nodes]
    edges = [{"source": u, "target": v, "weight": int(d.get("weight", 1))} for u, v, d in G.edges(data=True)]
    (out_dir / "tactic_graph.json").write_text(json.dumps({"nodes": nodes, "edges": edges}, indent=2))

    # Static PNG (simple spring layout).
    pos = nx.spring_layout(G, seed=0, k=1.2)
    plt.figure(figsize=(9, 6), dpi=160)
    node_sizes = [50 + 60 * (G.nodes[n]["count"] ** 0.5) for n in G.nodes]
    edge_widths = [0.6 + 0.6 * d.get("weight", 1) for _u, _v, d in G.edges(data=True)]
    nx.draw_networkx_edges(G, pos, width=edge_widths, alpha=0.35)
    nx.draw_networkx_nodes(G, pos, node_size=node_sizes, alpha=0.9)
    nx.draw_networkx_labels(G, pos, font_size=9)
    plt.title("Tactic co-occurrence graph (scanned from Lean sources)")
    plt.axis("off")
    plt.tight_layout()
    plt.savefig(out_dir / "tactic_graph.png")
    plt.close()

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
