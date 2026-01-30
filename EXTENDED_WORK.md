# Extended Work Log (append-only)

This is a running, append-only log of follow-on work after the initial “strict-only minimal” delivery.

**Principle:** keep this repo minimal. Any substantial HeytingLean integration code lives in the HeytingLean repo; we only reference it here.

## 2026-01-30T01:55:03Z — HeytingLean connector landed (strict-only)

We implemented the strict-only connector pieces in HeytingLean (not in this repo) so that `infinity-modal_thesis` stays minimal.

HeytingLean repo:
- `https://github.com/Abraxas1010/heyting`

Connector modules (Lean file paths in HeytingLean):
- `lean/HeytingLean/IteratedVirtual/Bridge/NucleusEnergy.lean`
  - Bridge: helix discrete tension energy → fixed point of a concrete `HeytingLean.Core.Nucleus` on `WithBot ℝ`.
- `lean/HeytingLean/IteratedVirtual/Bridge/MRClosure.lean`
  - Bridge: minimal `β`-closure operator packaged as a `HeytingLean.Core.Nucleus` when given extensivity + meet-preservation.
- `lean/HeytingLean/IteratedVirtual/Bridge/ModalSketch.lean`
  - Bridge: modal syntax + Gödel-style translation (no semantics / no GMT theorem claimed here).
- `lean/HeytingLean/Tests/IteratedVirtual/ExtendedNoahSanity.lean`
  - Sanity: compile-only checks for the above.

Notes:
- We deliberately did **not** add a Lake dependency from this repo to HeytingLean, to avoid pulling in the full codebase.
- Research-scale items from `WIP/extended_noah.txt` remain deferred until there is a scoped, strict-only plan.

## 2026-01-30T02:18:00Z — Repo minimization: remove `WIP/`

Change:
- Removed the `WIP/` directory from this repo (to keep the repo minimal and clean for researchers).
- Moved the append-only log to the repo root as `EXTENDED_WORK.md` (this file).

Operational note:
- The “Extended Work” section in `README.md` now describes the HeytingLean system-layer work in a unified way,
  while this log continues to record what has been *actually landed* and where.

## 2026-01-30T15:11:04Z — Phase-7 completion in HeytingLean (GMT + pasting coherence + strict QA)

HeytingLean repo:
- `https://github.com/Abraxas1010/heyting` (branch: `bh-algebrair2-codegen`)

New strict-only items landed (Lean file paths in HeytingLean):
- `lean/HeytingLean/IteratedVirtual/Pasting.lean`
  - Free pasting syntax for identity-framed virtual cells, with coherence as substitution laws
    (`Pasting.bind_assoc`, `Pasting.bind_pure_right`).
- `lean/HeytingLean/IteratedVirtual/Bridge/ModalCompanion.lean`
  - Gödel–McKinsey–Tarski modal companion bridge at the **provability** level:
    `Int ⊢ φ ↔ S4 ⊢ φᵍ`, re-exported from the `Foundation` library.

Supporting bridge pieces also landed (strict-only):
- `lean/HeytingLean/IteratedVirtual/Bridge/HelixAdelic.lean` (local/global decomposition + correct discrete periodicity when `step = 2π/n`)
- `lean/HeytingLean/IteratedVirtual/Bridge/MRSystemConnection.lean` (MR loop closure as idempotent projection + fixed points)
- `lean/HeytingLean/IteratedVirtual/Bridge/HeytingConnection.lean` (nucleus-commuting maps preserve fixed points)

Reproducibility note:
- `Foundation` was pinned to a fork/commit that is compatible with Mathlib `--wfail` (avoids a global name collision on `Matrix.map`).

Verification (HeytingLean):
- Strict library build: `cd lean && lake build --wfail`
- Executable builds: `./scripts/build_all_exes.sh --strict`
- Happy-path runs: `./scripts/run_all_exes.sh`

## 2026-01-30T17:04:29Z — Phase-8 progress: nontrivial bending/tension energy (strict-only)

Motivation:
- `SpiralEnergy.lean` proves “helix minimizes tension” for a *constraint energy* that is designed to be `0` on the helix.
- For Phase‑8 we also want an energy that is **not** zero-by-definition, and a theorem that characterizes its minimizers.

HeytingLean additions (strict-only):
- `lean/HeytingLean/IteratedVirtual/BendingEnergy.lean`
  - Discrete second-difference `Δ² p(k)` and bending energy `E(p, N) = ∑ ‖Δ² p(k)‖²`.
  - Theorem: `bendingEnergy_eq_zero_iff_secondDiff_eq_zero` (energy `0` iff all second differences vanish).
  - Theorem: `affine_on_prefix_of_secondDiff_eq_zero` (vanishing second differences ⇒ the curve is affine/straight on the prefix).
- `lean/HeytingLean/Tests/IteratedVirtual/BendingEnergySanity.lean`
  - Compile-only checks (including `zeroSeq` has energy `0`).

## 2026-01-30T17:06:42Z — Phase-8 progress: presheaf globular sets → structured globular sets

HeytingLean additions (strict-only):
- `lean/HeytingLean/IteratedVirtual/GlobularFromPresheaf.lean`
  - Adds `GlobularSetPsh.toGlobularSet` so presheaf globular semantics can be consumed by legacy modules expecting
    the minimal `GlobularSet` record.
- `lean/HeytingLean/Tests/IteratedVirtual/GlobularFromPresheafSanity.lean`

## 2026-01-30T17:53:59Z — Phase-8 progress: structured globular sets → presheaf globular sets

HeytingLean additions (strict-only):
- `lean/HeytingLean/IteratedVirtual/GlobularToPresheaf.lean`
  - Adds `GlobularSet.toPresheaf : GlobularSet → GlobularSetPsh`, complementing `toGlobularSet`.
- `lean/HeytingLean/Tests/IteratedVirtual/GlobularToPresheafSanity.lean`
  - Compile-only checks for `X.toPresheaf` and the round-trip `X.toPresheaf.toGlobularSet`.
- `lean/HeytingLean/IteratedVirtual/GlobularPresheaf.lean`
  - Makes `GlobularSetPsh` universe-polymorphic (`GlobularIndexᵒᵖ ⥤ Type u`) so conversions work for `GlobularSet.{u}`.

Note:
- We now have both directions as strict-only *bridges*, both round-trip isomorphisms, and a category equivalence.
- Remaining Phase‑8 “future work” is to replace/align `GlobularIndex` with the more standard “globe category”
  presentation (generators + relations / quotient), and re-run the equivalence proof against that presentation.

## 2026-01-30T21:10:00Z — Phase-8 progress: strict `Catₙ` as presheaf + “top cell” as globe-map (strict-only)

HeytingLean additions/changes (strict-only):
- `lean/HeytingLean/IteratedVirtual/NGlobularToGlobularEmpty.lean`
  - `NGlobularSet.toGlobularSetEmpty : NGlobularSet n → GlobularSet` by setting all cells above `n` to `PEmpty`.
  - Avoids choosing “(n+1)-cells” just to talk about `n`-cells.
- `lean/HeytingLean/IteratedVirtual/GlobularPresheaf.lean`
  - `GlobePsh` now uses `uliftYoneda` so representables land in `Type u` even though `GlobularIndex` is small.
- `lean/HeytingLean/IteratedVirtual/StrictNPresheaf.lean`
  - `StrictNCategory.toPresheaf` views a strict `n`-category as a presheaf globular set.
  - `cellTopPshOf` packages an `n`-cell as a map `GlobePsh n ⟶ C.toPresheaf` via `uliftYonedaEquiv`.
- `lean/HeytingLean/Tests/IteratedVirtual/StrictNPresheafSanity.lean`
  - Compile-only checks for `spiral22Cat` / `spiral22Params`.

## 2026-01-30T21:25:00Z — Phase-8 progress: structured→presheaf→structured round-trip iso (strict-only)

HeytingLean additions (strict-only):
- `lean/HeytingLean/IteratedVirtual/GlobularRoundTrip.lean`
  - `GlobularSet.toPresheaf_toGlobularSetIso : X.toPresheaf.toGlobularSet ≅ X`.
- `lean/HeytingLean/Tests/IteratedVirtual/GlobularRoundTripSanity.lean`
  - Compile-only check: `(Globe 3).toPresheaf_toGlobularSetIso`.

## 2026-01-30T19:36:21Z — Phase-8 progress: presheaf→structured→presheaf round-trip iso (strict-only)

HeytingLean additions (strict-only):
- `lean/HeytingLean/IteratedVirtual/GlobularRoundTripPsh.lean`
  - `GlobularSetPsh.toGlobularSet_toPresheafIso : (X.toGlobularSet).toPresheaf ≅ X`.
- `lean/HeytingLean/Tests/IteratedVirtual/GlobularRoundTripPshSanity.lean`
  - Compile-only check: `(GlobePsh 3).toGlobularSet_toPresheafIso`.

## 2026-01-30T19:50:04Z — Phase-8 progress: category equivalence `GlobularSet ≌ GlobularSetPsh` (strict-only)

HeytingLean additions (strict-only):
- `lean/HeytingLean/IteratedVirtual/GlobularEquivalence.lean`
  - `globularSetEquivalence : GlobularSet ≌ GlobularSetPsh`.
- `lean/HeytingLean/Tests/IteratedVirtual/GlobularEquivalenceSanity.lean`

## 2026-01-30T20:39:27Z — Phase-8 progress: presented globe category (generators+relations) + map into `GlobularIndex` (strict-only)

HeytingLean additions (strict-only):
- `lean/HeytingLean/IteratedVirtual/GlobeCategoryPresented.lean`
  - Presents the globe category `𝔾` as a quotient of the free path category on generators `σₙ, τₙ : n ⟶ n+1`,
    with the standard globular relations.
  - Provides `ToGlobularIndex.functor : GlobeCat ⥤ GlobularIndex.Obj` sending `σₙ ↦ src n`, `τₙ ↦ tgt n`.
- `lean/HeytingLean/Tests/IteratedVirtual/GlobeCategoryPresentedSanity.lean`

Verification (HeytingLean):
- Dev Mode QA: `./scripts/qa_dev.sh --files lean/HeytingLean/IteratedVirtual/GlobeCategoryPresented.lean lean/HeytingLean/Tests/IteratedVirtual/GlobeCategoryPresentedSanity.lean` PASSED.

## 2026-01-30T20:46:34Z — Phase-8 progress: constrained minimization theorem for bending energy (strict-only)

HeytingLean additions (strict-only):
- `lean/HeytingLean/IteratedVirtual/BendingEnergyMinimization.lean`
  - Defines `affineFrom01 a b` (affine extension from boundary points `p 0 = a`, `p 1 = b`).
  - Proves a discrete constrained minimization + uniqueness theorem: under these boundary constraints, the unique
    minimizer of `bendingEnergy` is `affineFrom01`.
- `lean/HeytingLean/Tests/IteratedVirtual/BendingEnergyMinimizationSanity.lean`

Verification (HeytingLean):
- Dev Mode QA: `./scripts/qa_dev.sh --files lean/HeytingLean/IteratedVirtual/BendingEnergyMinimization.lean lean/HeytingLean/Tests/IteratedVirtual/BendingEnergyMinimizationSanity.lean` PASSED.

## 2026-01-30T20:52:30Z — Phase-8 progress: spiral 22-cell as a presheaf globe-map (strict-only)

HeytingLean additions (strict-only):
- `lean/HeytingLean/IteratedVirtual/SpiralStrict22Presheaf.lean`
  - Exposes the spiral “22‑cell” as `GlobePsh 22 ⟶ spiral22Cat.toPresheaf` via `StrictNCategory.cellTopPshOf`.
- `lean/HeytingLean/Tests/IteratedVirtual/SpiralStrict22PresheafSanity.lean`

Verification (HeytingLean):
- Dev Mode QA: `./scripts/qa_dev.sh --files lean/HeytingLean/IteratedVirtual/SpiralStrict22Presheaf.lean lean/HeytingLean/Tests/IteratedVirtual/SpiralStrict22PresheafSanity.lean` PASSED.

## 2026-01-30T20:58:18Z — Phase-8 progress: non-identity-framed pasting syntax (strict-only)

HeytingLean additions (strict-only):
- `lean/HeytingLean/IteratedVirtual/PastingFramed.lean`
  - Generalizes the free pasting syntax to allow internal nodes with arbitrary vertical boundaries (`V.Cell`), not just
    identity-framed (“globular”) cells.
  - Proves substitution coherence (`bind_assoc`, units).
- `lean/HeytingLean/Tests/IteratedVirtual/PastingFramedSanity.lean`

Verification (HeytingLean):
- Dev Mode QA: `./scripts/qa_dev.sh --files lean/HeytingLean/IteratedVirtual/PastingFramed.lean lean/HeytingLean/Tests/IteratedVirtual/PastingFramedSanity.lean` PASSED.

## 2026-01-30T21:02:35Z — Phase-8 status: remaining research-scale items

Strict-only Phase‑8 items are now landed in HeytingLean (see the timestamped entries above).

Remaining research-scale items (not yet landed):
- Category equivalence between the presented globe category `GlobeCat` and the strict `GlobularIndex` surrogate, and a
  rebase of the presheaf globular semantics onto `GlobeCat` as the base category.
- An evaluation semantics for non-identity-framed pasting (beyond syntax-level substitution coherence), including an
  interchange law for a chosen composition semantics of `V.Cell`.
- A continuous (analysis-level) energy-minimization theorem (beyond the current strict-only discrete setting).
