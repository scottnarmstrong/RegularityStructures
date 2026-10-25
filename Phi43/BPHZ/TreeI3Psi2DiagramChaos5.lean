/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2DiagramN1Bound
public import Phi43.BPHZ.TreeI3Psi2DiagramN2Bound
public import Phi43.BPHZ.TreeI3Psi2DiagramTarget
public import Phi43.BPHZ.TreeI3PsiDiagramUniform

/-!
# Chaos `5` and chaos `3` double integrals of `I(Ψ³)Ψ²`

`∫∫ δK(z, w) δK(z', w') χ₅(w, w')` and `∫∫ δK(z, w) δK(z', w') χ₃(w, w')` are absolutely
integrable and bounded by `C · i3Psi2Target δ z z'`.  The kernels split as

* `χ₅ = 12 Q(z - z')² Q(w - w')³ + 72 Q(z - z') [chain] + 36 [N₁]`,
* `χ₃ = 72 Q(z - z') [chain] + 144 [N₂]`,

where the principal part `Q(w - w')³` is `i3PsiPrincipal`, the chains are `i3PsiChain` (with
the secondary and chaos-two centres respectively) and `N₁`, `N₂` are the new diagrams.
-/

public section

open MeasureTheory

namespace RegularityStructures

theorem i3Psi2_integrand5_eq (K Q : SpaceTime → ℝ) (hQe : ∀ x, Q (-x) = Q x) (z z' w v : SpaceTime) :
    i3Psi2dK K z w * i3Psi2dK K z' v * i3Psi2Chaos5 Q z z' w v =
      12 * Q (z - z') ^ 2 * i3PsiPrincipal K Q z z' w v +
        72 * Q (z - z') * i3PsiChain K Q z z' z' z w v + 36 * i3Psi2N1 K Q z z' w v := by
  have e := Q_sub_comm hQe z v
  unfold i3Psi2Chaos5 i3Psi2Kernel5 i3PsiPrincipal i3PsiChain i3Psi2N1 i3Psi2dK
  rw [e]
  ring

theorem i3Psi2_integrand3_eq (K Q : SpaceTime → ℝ) (hQe : ∀ x, Q (-x) = Q x) (z z' w v : SpaceTime) :
    i3Psi2dK K z w * i3Psi2dK K z' v * i3Psi2Chaos3 Q z z' w v =
      72 * Q (z - z') * i3PsiChain K Q z z' z z' w v + 144 * i3Psi2N2 K Q z z' w v := by
  have e := Q_sub_comm hQe z v
  unfold i3Psi2Chaos3 i3Psi2Kernel3 i3PsiChain i3Psi2N2 i3Psi2dK
  rw [e]
  ring

end RegularityStructures

end
