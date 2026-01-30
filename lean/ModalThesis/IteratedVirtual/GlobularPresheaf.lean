import Mathlib.CategoryTheory.Yoneda
import ModalThesis.IteratedVirtual.GlobularIndex

/-!
# IteratedVirtual.GlobularPresheaf

“True globular semantics” (strict-only): define globular sets as presheaves on the
globular indexing category `GlobularIndex`.

This provides:
- a canonical `GlobularSetPsh := GlobularIndexᵒᵖ ⥤ Type`,
- the induced `Cell`, `src`, `tgt` operations and globular identities,
- walking globes as representables `GlobePsh n := yoneda.obj (ofNat n)`,
- k-cells literally as maps `GlobePsh k ⟶ X`.
-/

namespace ModalThesis
namespace IteratedVirtual

open CategoryTheory

/-- A globular set as a presheaf on the globular indexing category. -/
abbrev GlobularSetPsh : Type 1 :=
  GlobularIndex.Objᵒᵖ ⥤ Type

namespace GlobularSetPsh

abbrev Cell (X : GlobularSetPsh) (n : Nat) : Type :=
  X.obj (Opposite.op (GlobularIndex.ofNat n))

def src {X : GlobularSetPsh} {n : Nat} : Cell X (n + 1) → Cell X n :=
  X.map (GlobularIndex.src n).op

def tgt {X : GlobularSetPsh} {n : Nat} : Cell X (n + 1) → Cell X n :=
  X.map (GlobularIndex.tgt n).op

theorem src_src_eq_src_tgt {X : GlobularSetPsh} {n : Nat} (x : Cell X (n + 2)) :
    src (n := n) (src (n := n + 1) x) = src (n := n) (tgt (n := n + 1) x) := by
  -- Use functoriality + the defining relation in `GlobularIndex`.
  have h :
      (GlobularIndex.src (n + 1)).op ≫ (GlobularIndex.src n).op =
        (GlobularIndex.tgt (n + 1)).op ≫ (GlobularIndex.src n).op := by
    simpa using congrArg Quiver.Hom.op (GlobularIndex.src_src_eq_src_tgt n)
  have := congrArg (fun f => X.map f x) h
  simpa [src, tgt, Functor.map_comp] using this

theorem tgt_src_eq_tgt_tgt {X : GlobularSetPsh} {n : Nat} (x : Cell X (n + 2)) :
    tgt (n := n) (src (n := n + 1) x) = tgt (n := n) (tgt (n := n + 1) x) := by
  have h :
      (GlobularIndex.src (n + 1)).op ≫ (GlobularIndex.tgt n).op =
        (GlobularIndex.tgt (n + 1)).op ≫ (GlobularIndex.tgt n).op := by
    simpa using congrArg Quiver.Hom.op (GlobularIndex.tgt_src_eq_tgt_tgt n)
  have := congrArg (fun f => X.map f x) h
  simpa [src, tgt, Functor.map_comp] using this

end GlobularSetPsh

/-- The walking `n`-globe as a **representable** presheaf on `GlobularIndex`. -/
def GlobePsh (n : Nat) : GlobularSetPsh :=
  yoneda.obj (GlobularIndex.ofNat n)

/-- A `k`-cell of a presheaf globular set `X` is literally a map `GlobePsh k ⟶ X`. -/
abbrev kCellPsh (X : GlobularSetPsh) (k : Nat) :=
  (GlobePsh k ⟶ X)

end IteratedVirtual
end ModalThesis
