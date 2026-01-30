# ∞-modal_thesis

Apoth3osis / ∞-modal: a **strict-only**, runnable Lean 4 artifact inspired by a public sketch about:
- iterated virtual (double) categorical structure,
- walking globes `Gₙ`,
- “k-cells as maps `Gₖ → Catₙ`”,
- and a “DNA-like spiral” emerging from an energy/tension minimization thought experiment.

This repo is intentionally **minimal and self-validating**: it builds, runs an executable that emits
spiral data as JSON, and regenerates a small set of static visuals (PNG/JSON) from scripts.

## Quickstart

### 1) Build (Lean)
```bash
lake build
```

### 2) Emit spiral points (JSON)
```bash
lake exe modal_thesis_spiral_dump -- --n 64 --step 0.35 --pitch 0.15 > docs/spiral_points.json
```

### 3) Regenerate visuals (Python)
```bash
./scripts/make_all_artifacts.sh
```

Outputs are written under `docs/`.

## “Spiral g” (the concrete visualization artifact)

We expose a concrete function (parameterized helix):

```
g(k) = (cos(step·k), sin(step·k), pitch·step·k)
```

Generated plots:

- 3D: `docs/spiral_g_3d.png`
- XY projection: `docs/spiral_g_xy.png`

![Spiral g(k) in 3D](docs/spiral_g_3d.png)
![Spiral g(k) XY](docs/spiral_g_xy.png)

## Mapping the original sketch → Lean identifiers (what is actually formalized)

The original thread explicitly framed the idea as “pure fantasy” and emphasized that the physics
analogy breaks down. This repo takes that seriously:

- We **do not** claim physical modeling of atomic bonds or DNA.
- We treat the spiral as a **visualization of formal compositional data**, and we prove only
  *mathematically internal* strict statements.

With that disclaimer, here is the direct mapping:

### Iterated virtual double category `V`
- Data-only “virtual double category”: `ModalThesis.IteratedVirtual.VirtualDoubleCategory`
  (`lean/ModalThesis/IteratedVirtual/Basic.lean`)
- Data-only “virtual equipment”: `ModalThesis.IteratedVirtual.VirtualEquipment`
  (`lean/ModalThesis/IteratedVirtual/Equipment.lean`)

### Walking k-globe `Gₙ`
We provide two layers (both strict-only):

1) A small explicit globular-set model: `ModalThesis.IteratedVirtual.Globe` (`lean/ModalThesis/IteratedVirtual/Globe.lean`)
2) “True globular semantics” as presheaves on an explicit globular indexing category:
   - `ModalThesis.IteratedVirtual.GlobularIndex` (`lean/ModalThesis/IteratedVirtual/GlobularIndex.lean`)
   - `ModalThesis.IteratedVirtual.GlobularSetPsh := GlobularIndexᵒᵖ ⥤ Type`
     (`lean/ModalThesis/IteratedVirtual/GlobularPresheaf.lean`)
   - representable walking globes: `ModalThesis.IteratedVirtual.GlobePsh n`

### “k-cell is a map `A : Gₖ → Catₙ`”
We make the slogan literal in the strict/truncated setting:

- Truncated strict `n`-categories: `ModalThesis.IteratedVirtual.StrictNCategory n`
  (`lean/ModalThesis/IteratedVirtual/StrictN.lean`)
- Top `n`-cells as globe-maps: `StrictNCategory.CellTop` (a map `GlobeN n ⟶ C.G`)
- For `k ≤ n`: `StrictNCategory.kCell`
- The “spiral as a literal 22-cell” example:
  - `ModalThesis.IteratedVirtual.spiral22Cat : StrictNCategory 22`
  - `ModalThesis.IteratedVirtual.spiral22Cell : GlobeN 22 ⟶ spiral22Cat.G`
    (`lean/ModalThesis/IteratedVirtual/SpiralStrict22.lean`)

### Iterated hom / “22 layers of meta-theory”
As a lightweight surrogate for “iterated hom” data, we include:
- `ModalThesis.IteratedVirtual.IteratedCell` and `IteratedCell22`
  (`lean/ModalThesis/IteratedVirtual/IteratedHom.lean`)

This is *not* presented as the full higher-categorical semantics of internal homs; it is a strict,
type-checking data model that can be refined later.

### Cobordisms + virtual composition
- Cobordisms between parallel arrows as a witness format:
  - `ModalThesis.IteratedVirtual.CobordismHom`, `CobordismOver`
    (`lean/ModalThesis/IteratedVirtual/Cobordism.lean`)
- “Virtual cells are virtual compositions of cobordisms”:
  - `ModalThesis.IteratedVirtual.CobordismChain` + strict associativity/unitality
    (`lean/ModalThesis/IteratedVirtual/VirtualComposition.lean`)

### “XY are cobordism-cells; Z is iteration level”
- A small “geometry view” of cobordism chains:
  - `ModalThesis.IteratedVirtual.spiralOfCobordismChain`
    (`lean/ModalThesis/IteratedVirtual/SpiralCobordism.lean`)

### “As k → ∞, a spiral minimizes tension”
We prove a deliberately modest, strict statement:

- Define a **nonnegative discrete energy** measuring deviation from helix constraints:
  `ModalThesis.IteratedVirtual.Point3R.tensionEnergyAt`
- Prove the helix achieves energy `0`, hence minimizes (pointwise and on lists):
  `Point3R.helix_minimizes_pointwise`, `Point3R.helix_minimizes_list`
- “k → ∞” (atTop) statement:
  `Point3R.tendsto_tensionEnergyAt_helix_atTop`

All of these live in `lean/ModalThesis/IteratedVirtual/SpiralEnergy.lean`.

## UMAP + tactic graphs (lightweight, local)

This repo includes small, reproducible scripts to generate:

- UMAP of the local import graph:
  - 2D plot: `docs/umap_imports_2d.png`
  - 3D embedding: `docs/umap_imports_3d.json`
- Tactic co-occurrence graph:
  - plot: `docs/tactic_graph.png`
  - data: `docs/tactic_graph.json`

![UMAP imports 2D](docs/umap_imports_2d.png)
![Tactic graph](docs/tactic_graph.png)

## CT-friendly diagram tooling (recommended)

For interactive globular/pasting-diagram work (not bundled), see `research/ct_visualization_tools.md`,
including:
- https://globular.science/
- https://homotopy.io/
- https://q.uiver.app/ (export to tikz-cd)

## Notes

- This directory name contains Unicode (`∞-modal_thesis`). If any tooling struggles, clone/copy the repo
  into an ASCII path; the Lean code is independent of the folder name.

