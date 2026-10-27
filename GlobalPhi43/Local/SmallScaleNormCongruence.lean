module

public import GlobalPhi43.MW20.ExtendedKernelProducts

public section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Set
open scoped ContDiff Topology

/-- Equality of local fields preserves the actual expansion on the product domain. -/
theorem sourceExpansion_eqOn {v w Y Z : ParabolicSpace → ℝ} {D : Set ParabolicSpace}
    (h : EqOn v w D) : EqOn (sourceExpansion v Y Z) (sourceExpansion w Y Z) (D ×ˢ D) := by
  rintro ⟨x,y⟩ ⟨hx,hy⟩
  simp only [sourceExpansion, expansion_eq, h hx, h hy]

end GlobalPhi43.Local
