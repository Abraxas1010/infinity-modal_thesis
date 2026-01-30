import ModalThesis.IteratedVirtual.IteratedHom

/-!
# IteratedVirtual.Cobordism

A minimal “cobordism between parallel n-cells” notion, generalizing the existing SKY
`PathHomotopy` shape: two morphisms become equal after postcomposition by possibly different
morphisms.

This is deliberately weak/data-only: it is a reusable *witness format* that can later be
related to `VirtualDoubleCategory.Cell` for specific instances (e.g. CommSq-based examples).
-/

namespace ModalThesis
namespace IteratedVirtual

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C]

/-- A cobordism between two parallel `n`-cells `A,B : X ⟶ Y`:
there exists a “capping” object `Z` and morphisms `r₁ r₂ : Y ⟶ Z` such that
`A ≫ r₁ = B ≫ r₂`. -/
structure CobordismOver {X Y : C} {n : Nat}
    (A B : IteratedCellOver (C := C) X Y n) where
  Z : C
  r₁ : Y ⟶ Z
  r₂ : Y ⟶ Z
  comm : A.hom ≫ r₁ = B.hom ≫ r₂

namespace CobordismOver

def refl {X Y : C} {n : Nat} (A : IteratedCellOver (C := C) X Y n) : CobordismOver (C := C) A A :=
  { Z := Y
    r₁ := 𝟙 Y
    r₂ := 𝟙 Y
    comm := by simp [IteratedCellOver.hom] }

def symm {X Y : C} {n : Nat} {A B : IteratedCellOver (C := C) X Y n} :
    CobordismOver (C := C) A B → CobordismOver (C := C) B A := by
  intro h
  refine { Z := h.Z, r₁ := h.r₂, r₂ := h.r₁, comm := ?_ }
  simpa using h.comm.symm

end CobordismOver

/-!
## Cobordisms between parallel morphisms

For ordinary morphisms `f,g : X ⟶ Y`, we package them as `n = 1` cells via `IteratedCellOver.ofHom`.
-/

abbrev CobordismHom {X Y : C} (f g : X ⟶ Y) : Type (max u v) :=
  CobordismOver (C := C) (A := IteratedCellOver.ofHom (C := C) f) (B := IteratedCellOver.ofHom (C := C) g)

namespace CobordismHom

def refl {X Y : C} (f : X ⟶ Y) : CobordismHom (C := C) f f :=
  CobordismOver.refl (C := C) (A := IteratedCellOver.ofHom (C := C) f)

def symm {X Y : C} {f g : X ⟶ Y} : CobordismHom (C := C) f g → CobordismHom (C := C) g f := by
  intro h
  exact CobordismOver.symm (C := C) h

end CobordismHom

end IteratedVirtual
end ModalThesis
