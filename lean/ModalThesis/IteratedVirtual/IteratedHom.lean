import Mathlib.CategoryTheory.Category.Basic

/-!
# IteratedVirtual.IteratedHom

A lightweight “iterated hom / k-cell” surrogate, intended only to give a stable,
compilable notion of “n-cell data” that can later be refined to true globular/higher
categorical semantics.

In this MVP, an `IteratedCell C n` is a **formal chain of composable vertical arrows**
of length `n` in a category `C`.
-/

namespace ModalThesis
namespace IteratedVirtual

universe u v

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- A formal composable chain of morphisms in a category. -/
inductive VChain : C → C → Type (max u v)
  | nil (X : C) : VChain X X
  | cons {X Y Z : C} : (X ⟶ Y) → VChain Y Z → VChain X Z

namespace VChain

def length {X Y : C} : VChain X Y → Nat
  | nil _ => 0
  | cons _ rest => rest.length.succ

def comp {X Y : C} : VChain X Y → (X ⟶ Y)
  | nil X => 𝟙 X
  | cons f rest => f ≫ rest.comp

@[simp] theorem comp_nil (X : C) : (VChain.nil X).comp = 𝟙 X := rfl

@[simp] theorem length_nil (X : C) : (VChain.nil X).length = 0 := rfl

@[simp] theorem length_cons {X Y Z : C} (f : X ⟶ Y) (rest : VChain Y Z) :
    (VChain.cons f rest).length = rest.length.succ := rfl

/-- A length-`n` chain of identity morphisms. -/
def idRep (X : C) : Nat → VChain X X
  | 0 => VChain.nil X
  | n + 1 => VChain.cons (𝟙 X) (idRep X n)

@[simp] theorem length_idRep (X : C) (n : Nat) : (idRep X n).length = n := by
  induction n with
  | zero =>
      simp [idRep]
  | succ n ih =>
      simp [idRep, ih]

end VChain

/-- “n-cell data” as a chain of exactly `n` composable morphisms. -/
structure IteratedCell (n : Nat) where
  src : C
  tgt : C
  chain : VChain src tgt
  length_eq : chain.length = n

/-!
## Endpoint-fixed variant

For “cobordism between parallel n-cells” it is often convenient to keep endpoints explicit
in the type, avoiding transports across `src/tgt` equalities.
-/

/-- An `n`-step chain from a fixed source `X` to a fixed target `Y`. -/
structure IteratedCellOver (X Y : C) (n : Nat) where
  chain : VChain (C := C) X Y
  length_eq : chain.length = n

namespace IteratedCellOver

def hom {X Y : C} {n : Nat} (A : IteratedCellOver (C := C) X Y n) : X ⟶ Y :=
  A.chain.comp

/-- View an `IteratedCellOver` as an `IteratedCell`. -/
def toIteratedCell {X Y : C} {n : Nat} (A : IteratedCellOver (C := C) X Y n) : IteratedCell (C := C) n :=
  { src := X, tgt := Y, chain := A.chain, length_eq := A.length_eq }

/-- A single-arrow `IteratedCellOver` (length `1`). -/
def ofHom {X Y : C} (f : X ⟶ Y) : IteratedCellOver (C := C) X Y 1 :=
  { chain := VChain.cons f (VChain.nil Y)
    length_eq := by simp }

@[simp] theorem hom_ofHom {X Y : C} (f : X ⟶ Y) : (ofHom (C := C) f).hom = f := by
  simp [hom, ofHom, VChain.comp]

end IteratedCellOver

abbrev Cell22 : Type (max u v) :=
  IteratedCell (C := C) 22

end IteratedVirtual
end ModalThesis
