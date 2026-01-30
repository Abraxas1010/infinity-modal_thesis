import ModalThesis.IteratedVirtual.SpiralStrict22

/-!
# Tests.IteratedVirtual.StrictNSpiralSanity

Compile-only sanity checks for the Phase 6 “true Catₙ” layer:
- `StrictNCategory` (truncated, no `(n+1)` requirement),
- the walking `n`-globe `GlobeN n`,
- and a literal “spiral as a 22-cell” example.
-/

namespace ModalThesis
namespace Tests
namespace IteratedVirtual

open ModalThesis.IteratedVirtual

#check ModalThesis.IteratedVirtual.NGlobularSet
#check ModalThesis.IteratedVirtual.GlobeN
#check ModalThesis.IteratedVirtual.StrictNCategory

-- The spiral 22-category and its canonical 22-cell exist.
#check ModalThesis.IteratedVirtual.spiral22Cat
#check ModalThesis.IteratedVirtual.spiral22Cell

end IteratedVirtual
end Tests
end ModalThesis
