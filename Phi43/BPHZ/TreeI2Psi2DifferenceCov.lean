/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2DifferenceMajorant
public import Phi43.Stochastic.ConstantsComparisonDefinitions

/-!
# The mean of the field of `I(Ψ²) Ψ²`

`i2Psi2Mean`: the mean `m_s(y) = -2 ∫ K(x - w) Q_s(w - y)² dw` of the field of `I(Ψ²) Ψ²` at
scale `s`. In the covariance of the two-scale difference of the field, split by chaos
([Hai14, (10.3)] for `τ = I(Ψ²) Ψ²`), the chaos-`0` part is the product
`(m_a(y) - m_b(y)) (m_a(y') - m_b(y'))` of the differences of the means.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- The mean `m_s(y) = -2 ∫ K(x - w) Q_s(w - y)² dw` of the field of `I(Ψ²) Ψ²` at scale `s`. -/
def i2Psi2Mean (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (x : SpaceTime) (s : ℝ) (y : SpaceTime) : ℝ :=
  -2 * ∫ w, hairerKernelTorus N (x - w) * hairerCovariance N ρ s (w - y) ^ 2

end RegularityStructures.Phi43

end

