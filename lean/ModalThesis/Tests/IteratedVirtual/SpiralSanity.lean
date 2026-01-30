import ModalThesis.IteratedVirtual.Spiral

/-!
Compile-only sanity: spiral embedding functions elaborate.
-/

namespace ModalThesis
namespace Tests
namespace IteratedVirtual

open ModalThesis.IteratedVirtual

#check ModalThesis.IteratedVirtual.Point3
#check ModalThesis.IteratedVirtual.embedSteps

example : (ModalThesis.IteratedVirtual.embedSteps 0).length = 1 := by
  simp [ModalThesis.IteratedVirtual.embedSteps]

end IteratedVirtual
end Tests
end ModalThesis
