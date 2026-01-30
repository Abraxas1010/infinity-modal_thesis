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
