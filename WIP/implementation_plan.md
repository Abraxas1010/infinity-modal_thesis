# Implementation Plan: ∞-modal_thesis (minimal, runnable)
**Date:** 2026-01-30

Goal: a *standalone* repository that a researcher can clone and run to:
1) build the Lean formalization (strict-only; no `sorry`),
2) run an executable that emits spiral data,
3) regenerate the key visuals (spiral plots, UMAP plots, tactic graph).

## Phase A — Lean core (strict-only)

Deliverables (already present under `lean/ModalThesis/IteratedVirtual/`):
- `VirtualDoubleCategory`, `VirtualEquipment` (data-only scaffolding).
- Globular semantics:
  - explicit globular indexing category `GlobularIndex`,
  - presheaf globular sets `GlobularSetPsh := GlobularIndexᵒᵖ ⥤ Type`,
  - walking globes as representables `GlobePsh n`,
  - “k-cell” as literal globe-map `GlobePsh k ⟶ X`.
- Truncated strict `n`-categories (`StrictNCategory`) + walking `n`-globe `GlobeN n`.
- A “spiral as a literal 22-cell” example: `IteratedVirtual.spiral22Cat`, `IteratedVirtual.spiral22Cell`.
- Discrete “tension energy” and minimization statement: `IteratedVirtual.Point3R.*` in `SpiralEnergy.lean`.

Acceptance:
- `lake build` succeeds.
- Sanity modules compile:
  - `ModalThesis.Tests.IteratedVirtual.NoahRequirementsSanity`
  - `ModalThesis.Tests.IteratedVirtual.GlobularIndexSanity`
  - `ModalThesis.Tests.IteratedVirtual.StrictNSpiralSanity`
  - `ModalThesis.Tests.IteratedVirtual.StrictNKCellSanity`

## Phase B — Executable artifact

Deliverable:
- `lake exe modal_thesis_spiral_dump` emits JSON points (happy path, no args).

Acceptance:
- Running the executable exits 0 and prints a JSON array.

## Phase C — Visual artifacts (local regeneration)

Deliverables:
- `scripts/gen_spiral_data.sh` → `docs/spiral_points.json`
- `scripts/viz_spiral.py` → `docs/spiral_g_xy.png`, `docs/spiral_g_3d.png`
- `scripts/umap_import_graph.py` → `docs/umap_imports_2d.png`, `docs/umap_imports_3d.json`
- `scripts/tactic_graph.py` → `docs/tactic_graph.png`, `docs/tactic_graph.json`

Acceptance:
- `./scripts/make_all_artifacts.sh` runs end-to-end.

## Phase D — “Noah thread” mapping in README

Deliverable:
- README section translating the bullet list to Lean identifiers in this repo,
  and explicitly separating:
  - the formalized strict core,
  - the geometric visualization layer,
  - and the non-physical / “fantasy” disclaimer.

