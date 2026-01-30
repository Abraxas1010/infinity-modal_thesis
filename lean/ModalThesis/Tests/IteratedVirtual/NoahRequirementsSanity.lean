import ModalThesis.IteratedVirtual.KCellCobordism
import ModalThesis.IteratedVirtual.SpiralCobordism
import ModalThesis.IteratedVirtual.StrictOmega
import ModalThesis.IteratedVirtual.SpiralEnergy

/-!
# Tests.IteratedVirtual.NoahRequirementsSanity

Compile-only sanity checks that the “Noah requirements” interfaces exist:
- k-cells as globe-maps,
- cobordisms and virtual compositions between k-cells (as morphisms in `GlobularSet`),
- a `k → ∞` (atTop) tension-minimization statement for the helix energy functional.
-/

namespace ModalThesis
namespace Tests
namespace IteratedVirtual

open ModalThesis.IteratedVirtual

-- `GlobularSet` is a category; k-cells are morphisms.
#check (inferInstance : CategoryTheory.Category ModalThesis.IteratedVirtual.GlobularSet)
#check ModalThesis.IteratedVirtual.kCell
#check ModalThesis.IteratedVirtual.KCellCobordism
#check ModalThesis.IteratedVirtual.KCellVirtualCobordism

-- Trivial “Catₙ” example exists and has a 22-cell.
def terminal_cell22' :
    ModalThesis.IteratedVirtual.StrictNCat.Cell22 (ModalThesis.IteratedVirtual.Examples.terminalNCat 22) :=
  { map := fun _ _ => PUnit.unit
    map_src := by intro n x; rfl
    map_tgt := by intro n x; rfl }

-- A cobordism between parallel k-cells (here: the same k-cell).
def terminal_kcell (k : Nat) :
    ModalThesis.IteratedVirtual.kCell (X := ModalThesis.IteratedVirtual.Examples.terminalGlobularSet) k :=
  { map := fun _ _ => PUnit.unit
    map_src := by intro n x; rfl
    map_tgt := by intro n x; rfl }

def terminal_kcell_cobordism (k : Nat) :
    ModalThesis.IteratedVirtual.KCellCobordism
      (X := ModalThesis.IteratedVirtual.Examples.terminalGlobularSet) k (terminal_kcell k) (terminal_kcell k) :=
  ModalThesis.IteratedVirtual.CobordismHom.refl (C := ModalThesis.IteratedVirtual.GlobularSet) (terminal_kcell k)

-- Virtual composition: trivial chain.
def terminal_kcell_virtual (k : Nat) :
    ModalThesis.IteratedVirtual.KCellVirtualCobordism
      (X := ModalThesis.IteratedVirtual.Examples.terminalGlobularSet) k (terminal_kcell k) (terminal_kcell k) :=
  ModalThesis.IteratedVirtual.VirtualCobordismHom.refl (C := ModalThesis.IteratedVirtual.GlobularSet) (terminal_kcell k)

-- “k → ∞” (atTop) helix energy tends to 0.
example (pitch : ℝ) :
    Filter.Tendsto
      (fun k : Nat =>
        ModalThesis.IteratedVirtual.Point3R.tensionEnergyAt (t := (k : ℝ)) pitch
          (ModalThesis.IteratedVirtual.Point3R.helix (t := (k : ℝ)) pitch))
      Filter.atTop (nhds (0 : ℝ)) :=
  ModalThesis.IteratedVirtual.Point3R.tendsto_tensionEnergyAt_helix_atTop pitch

end IteratedVirtual
end Tests
end ModalThesis
