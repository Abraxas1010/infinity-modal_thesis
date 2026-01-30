# CT Visualization Tools (Selection Notes)
**Date:** 2026-01-30

This repo aims to be runnable locally with *minimal* dependencies, while still producing visuals that
category theorists will recognize.

## Higher-category / globular diagram tools (interactive, external)

These are the best “native” environments we found for globular/pasting-diagram intuition. They are
not bundled here (web apps), but the README links to them because they are the right UX for CT work.

- **Globular** — interactive higher-category proof assistant / pasting diagrams.  
  Website: https://globular.science/
- **homotopy.io** — interactive diagrams for (higher) category theory and homotopy type theory.  
  Website: https://homotopy.io/

## Commutative-diagram tools (authoring)

- **Quiver** — web editor for commutative diagrams; exports LaTeX (tikz-cd).  
  Website: https://q.uiver.app/
- **tikz-cd** — standard LaTeX commutative diagram package (best for papers).  
  CTAN: https://ctan.org/pkg/tikz-cd

## What we bundle locally (reproducible scripts)

Because GitHub READMEs do not render tikz-cd directly, we generate **PNG** artifacts:

- `docs/spiral_g_3d.png`, `docs/spiral_g_xy.png` from `scripts/viz_spiral.py`
- `docs/umap_imports_2d.png` (+ `docs/umap_imports_3d.json`) from `scripts/umap_import_graph.py`
- `docs/tactic_graph.png` (+ `docs/tactic_graph.json`) from `scripts/tactic_graph.py`

This keeps the repo self-validating (run scripts → regenerate images), while still pointing CT users
to the best-in-class interactive tools for globular semantics.

