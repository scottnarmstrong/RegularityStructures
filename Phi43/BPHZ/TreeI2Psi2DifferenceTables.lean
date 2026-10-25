/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2DiagramDiffBound
public import Mathlib.Algebra.Order.Star.Real
public import Phi43.BPHZ.TreeI3PsiDifferenceAlgebra

/-!
# The `2 × 2` tables of cross covariances: uniform bound data

The bound data `Bd μ P Q` of the tables `(a, b, c, d)`, `(a, a, d, d)`, `(a, d, a, d)` of cross
covariances, `μ = (max ε ε')^θ`, enter the second difference of the chaos kernels of `I(Ψ²) Ψ²`
with weights both at `s(z)` and at `s(-z)` (the orientation of the kernel increments). The bound
data are therefore used in a uniform form, through the monotonicity of `Bd` in `P` and `Q`
(`i2Psi2DiffTableBd_mono`).
-/

public section

namespace RegularityStructures.Phi43

open RegularityStructures

/-- `Bd μ P Q t` is monotone in `P` and `Q`. -/
theorem i2Psi2DiffTableBd_mono {μ P Q P' Q' : ℝ} {t : I3PsiDiffTable} (hμ : 0 ≤ μ)
    (hQ : 0 ≤ Q) (hP : P ≤ P') (hQQ : Q ≤ Q') (h : I3PsiDiffTable.Bd μ P Q t) :
    I3PsiDiffTable.Bd μ P' Q' t := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hP0 : 0 ≤ P := (abs_nonneg _).trans h1
  have hQ' : 0 ≤ Q' := hQ.trans hQQ
  have hP' : 0 ≤ P' := hP0.trans hP
  have e1 : μ * P * Q ≤ μ * P' * Q' :=
    mul_le_mul (mul_le_mul_of_nonneg_left hP hμ) hQQ hQ (mul_nonneg hμ hP')
  have e2 : μ ^ 2 * P * Q ^ 2 ≤ μ ^ 2 * P' * Q' ^ 2 :=
    mul_le_mul (mul_le_mul_of_nonneg_left hP (sq_nonneg μ)) (pow_le_pow_left₀ hQ hQQ 2)
      (sq_nonneg Q) (mul_nonneg (sq_nonneg μ) hP')
  exact ⟨h1.trans hP, h2.trans hP, h3.trans hP, h4.trans hP, h5.trans e1, h6.trans e1,
    h7.trans e2⟩

end RegularityStructures.Phi43

end
