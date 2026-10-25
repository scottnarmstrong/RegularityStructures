/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3PsiPowers

/-!
# The abstract covariance of the tree `I(Ψ³)Ψ²`

For a kernel `K` (the singular kernel) and a covariance `Q` (a mollified two-point function)
write `δK(z, w) = K(z - w) - K(-w)` (base point `0`).  The covariance of the field
`(Π̂^ε_0 τ)(z) = (δK ∗ :Ψ³:)(z) :Ψ²:(z) - 3 C₂ Ψ(z)`, `τ = I(Ψ³)Ψ²`, of `Phi43.BPHZ.TreeI3Psi2Field*`
(`hairerI3Psi2Field_integral_mul`, `hairerI3Psi2Cov`) is, at a single scale, the expression
`i3Psi2Cov K Q c z z'`, with `c = C₂` and the chaos-`5`, `3`, `1` kernels
`χ₅, χ₃, χ₁` of the product of two Wick cubes and two Wick squares evaluated at the points
`(w, z, w', z')`, the cross terms with the counterterm `-3 C₂ Ψ`, and the term `9 C₂² Q(z - z')`.
The entries are `c₀₂ = Q(w - w')`, `c₀₃ = Q(w - z')`, `c₁₂ = Q(z - w')`, `c₁₃ = Q(z - z')`,
`c₀₁ = Q(w - z)`, `c₂₃ = Q(w' - z')`, exactly as in `hairerI3Psi2Chaos5/3/1`.

Source: [Hai14] = arXiv:1303.5113v4, p. 170--171.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures

/-- The recentred kernel `δK(z, w) = K(z - w) - K(-w)` (base point `0`). -/
def i3Psi2dK (K : SpaceTime → ℝ) (z w : SpaceTime) : ℝ := K (z - w) - K (-w)

/-- The chaos-`5` kernel in terms of the entries `c₀₂, c₀₃, c₁₂, c₁₃`. -/
def i3Psi2Kernel5 (c02 c03 c12 c13 : ℝ) : ℝ :=
  12 * c02 ^ 3 * c13 ^ 2 + 72 * c02 ^ 2 * c03 * c12 * c13 + 36 * c02 * c03 ^ 2 * c12 ^ 2

/-- The chaos-`3` kernel in terms of the entries `c₀₁, c₂₃, c₀₂, c₀₃, c₁₂, c₁₃`. -/
def i3Psi2Kernel3 (c01 c23 c02 c03 c12 c13 : ℝ) : ℝ :=
  72 * c01 * c02 ^ 2 * c13 * c23 + 144 * c01 * c02 * c03 * c12 * c23

/-- The chaos-`1` kernel in terms of the entries `c₀₁, c₂₃, c₀₂`. -/
def i3Psi2Kernel1 (c01 c23 c02 : ℝ) : ℝ :=
  36 * c01 ^ 2 * c02 * c23 ^ 2

/-- The chaos-`5` kernel `χ₅(w, w')` at the points `(w, z, w', z')`. -/
def i3Psi2Chaos5 (Q : SpaceTime → ℝ) (z z' w w' : SpaceTime) : ℝ :=
  i3Psi2Kernel5 (Q (w - w')) (Q (w - z')) (Q (z - w')) (Q (z - z'))

/-- The chaos-`3` kernel `χ₃(w, w')` at the points `(w, z, w', z')`. -/
def i3Psi2Chaos3 (Q : SpaceTime → ℝ) (z z' w w' : SpaceTime) : ℝ :=
  i3Psi2Kernel3 (Q (w - z)) (Q (w' - z')) (Q (w - w')) (Q (w - z')) (Q (z - w')) (Q (z - z'))

/-- The chaos-`1` kernel `χ₁(w, w')` at the points `(w, z, w', z')`. -/
def i3Psi2Chaos1 (Q : SpaceTime → ℝ) (z z' w w' : SpaceTime) : ℝ :=
  i3Psi2Kernel1 (Q (w - z)) (Q (w' - z')) (Q (w - w'))

/-- The chaos-`k` double integral `∫∫ δK(z, w) δK(z', w') χ_k(w, w') dw dw'` over the product. -/
def i3Psi2Double (K : SpaceTime → ℝ) (χ : SpaceTime → SpaceTime → SpaceTime → SpaceTime → ℝ)
    (z z' : SpaceTime) : ℝ :=
  ∫ q : SpaceTime × SpaceTime, i3Psi2dK K z q.1 * i3Psi2dK K z' q.2 * χ z z' q.1 q.2

/-- **The covariance of the field of `I(Ψ³)Ψ²`**, at one scale: the three chaos integrals, the two
cross terms with the counterterm `-3 c Ψ` (`c = C₂`), and `9 c² Q(z - z')`.  This is
`hairerI3Psi2Cov N ρ 0 a a z z'` for `K = hairerKernelTorus N`, `Q = hairerCovariance N ρ a`,
`c = hairerSunsetConstant N ρ a`. -/
def i3Psi2Cov (K Q : SpaceTime → ℝ) (c : ℝ) (z z' : SpaceTime) : ℝ :=
  i3Psi2Double K (i3Psi2Chaos5 Q) z z' + i3Psi2Double K (i3Psi2Chaos3 Q) z z' +
    i3Psi2Double K (i3Psi2Chaos1 Q) z z' -
  3 * c * (∫ w, i3Psi2dK K z w * (6 * Q (w - z) ^ 2 * Q (w - z'))) -
  3 * c * (∫ w, i3Psi2dK K z' w * (6 * Q (w - z') ^ 2 * Q (w - z))) +
  9 * c * c * Q (z - z')

/-- The target majorant of [Hai14, p. 170--171] with the pairs `(0, -1-δ)`, `(1-δ, -2)`,
`(-δ, -1)`, `(-1-2δ, 0)`. -/
def i3Psi2Target (δ : ℝ) (z z' : SpaceTime) : ℝ :=
  torusParabolicSize (z - z') ^ (-(1 + δ)) +
    torusParabolicSize (z - z') ^ (-(2 : ℝ)) *
      (torusParabolicSize z ^ (1 - δ) + torusParabolicSize z' ^ (1 - δ)) +
    torusParabolicSize (z - z') ^ (-(1 : ℝ)) *
      (torusParabolicSize z ^ (-δ) + torusParabolicSize z' ^ (-δ)) +
    torusParabolicSize z ^ (-(1 + 2 * δ)) + torusParabolicSize z' ^ (-(1 + 2 * δ))

end RegularityStructures

end
