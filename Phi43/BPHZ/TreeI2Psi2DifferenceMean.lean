/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2DifferenceCov
public import Phi43.BPHZ.TreeI2Psi2TestedCov
public import Phi43.BPHZ.TreeI3PsiDifferenceAlgebra
public import Phi43.BPHZ.TreeI2Psi2DiagramMultiBasic

/-!
# The difference of the means of the field of `I(Ψ²) Ψ²`: ingredients

The mean of the field of `I(Ψ²) Ψ²` at scale `s` is `m_s(y) = -2 ∫ K(x - w) Q_s(w - y)² dw`.
Its two-scale difference is bounded through the table `(Q_a, Q_a, Q_b, Q_b)`:
`|Q_a - Q_b| ≲ (max a b)^θ s^(-1-θ)` and `|Q_a + Q_b| ≲ s^(-1)` give
`|Q_a² - Q_b²| ≲ (max a b)^θ s^(-2-θ)` (`abs_sq_sub_sq_le_of_bd`); the total order `5 + θ` of
`|K| s^(-2-θ)` is above the critical `5`, so there is no logarithmic loss
(`integrable_and_abs_integral_diff_chaos0_le`). Also: `i2Psi2KernelHyp_hairerKernelTorus`, the
kernel hypotheses of the diagram estimates for the torus kernel. The bound itself, for two
mollifiers, is in `Phi43.BPHZ.TreeI2Psi2CrossMean`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The kernel `hairerKernelTorus N` satisfies the hypotheses of the diagram estimates. -/
theorem i2Psi2KernelHyp_hairerKernelTorus (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ i2Psi2KernelHyp (hairerKernelTorus N) B := by
  obtain ⟨CK, hCK, hK⟩ := constantsComparison_hairerKernelTorus_uniform_singular_bound_unconditional N
  obtain ⟨Ci, hCi, hi⟩ := hairerKernelTorus_sub_abs_le N
  refine ⟨CK + Ci, by linarith, by linarith, measurable_constantsComparison_hairerKernelTorus N,
    fun z hz => hairerKernelTorus_eq_zero_of_one_lt_time N hz, fun z hz => ?_, fun u h hu hh => ?_⟩
  · exact (hK hz).trans (mul_le_mul_of_nonneg_right (by linarith)
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
  · exact (hi hu hh).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) (torusParabolicSize_nonneg _))
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))

/-- From the bound data of the table `(x, x, y, y)`: `|x² - y²| ≤ 4 μ P² Q`. -/
theorem abs_sq_sub_sq_le_of_bd {μ P Q u v : ℝ} (h : I3PsiDiffTable.Bd μ P Q ⟨u, u, v, v⟩) :
    |u ^ 2 - v ^ 2| ≤ 4 * μ * P ^ 2 * Q := by
  obtain ⟨h1, -, -, -, h5, -, -⟩ := h
  have hP : 0 ≤ P := (abs_nonneg _).trans h1
  simp only [I3PsiDiffTable.mean, I3PsiDiffTable.du] at h1 h5
  have e1 : u ^ 2 - v ^ 2 = (u - v) * (u + v) := by ring
  have a1 : |u + v| ≤ 2 * P := by
    have : u + v = 2 * ((u + u + v + v) / 4) := by ring
    rw [this, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have a2 : |u - v| ≤ 2 * (μ * P * Q) := by
    have : u - v = 2 * ((u + u - v - v) / 4) := by ring
    rw [this, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hnn : 0 ≤ 2 * (μ * P * Q) := (abs_nonneg _).trans a2
  rw [e1, abs_mul]
  calc |u - v| * |u + v| ≤ 2 * (μ * P * Q) * (2 * P) := mul_le_mul a2 a1 (abs_nonneg _) hnn
    _ = _ := by ring

end RegularityStructures.Phi43

end
