/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3PsiDiagramMultiPointwise
public import Phi43.BPHZ.TreeI3PsiTestedPairing
public import Phi43.BPHZ.TreePsiDifference

/-!
# Inputs of the chain pieces of the difference diagram of `I(Ψ³)Ψ`

With `K = hairerKernelTorus N` and `δK(z, w) = K(z - w) - K(-w)`, the chain pieces of the second
difference of the block kernels of `I(Ψ³)Ψ` are integrals over `(w, v)` of `δK(z,w) δK(z',v)`
times second differences of the cross covariances. This module provides two of their inputs:

* `hairerKernelTorus_diagram_data`: the bounds on `K` used by the diagram lemmas (measurability,
  time support in `|t| ≤ 1`, `|K x| ≲ s(x)^(-3)` and the increment bound
  `|K(u + h) - K(u)| ≲ s(h) s(u)^(-4)` for `s(h) ≤ s(u)/2`);
* `ae_ae_chain_pos`: almost every `(w, v)` has positive distances to the centres.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The bounds on the kernel used by the diagram lemmas. -/
theorem hairerKernelTorus_diagram_data (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ Measurable (hairerKernelTorus N) ∧
      (∀ x : SpaceTime, 1 < |x.1| → hairerKernelTorus N x = 0) ∧
      (∀ x, 0 < torusParabolicSize x →
        |hairerKernelTorus N x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) ∧
      (∀ u h : SpaceTime, 0 < torusParabolicSize u → torusParabolicSize h ≤ torusParabolicSize u / 2 →
        |hairerKernelTorus N (u + h) - hairerKernelTorus N u| ≤
          B * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ))) := by
  obtain ⟨CK, hCK, hK⟩ := constantsComparison_hairerKernelTorus_uniform_singular_bound_unconditional N
  obtain ⟨Ci, hCi, hi⟩ := hairerKernelTorus_sub_abs_le N
  refine ⟨CK + Ci, by linarith, measurable_constantsComparison_hairerKernelTorus N,
    fun x hx => hairerKernelTorus_eq_zero_of_one_lt_time N hx, fun z hz => ?_, ?_⟩
  · exact (hK hz).trans (mul_le_mul_of_nonneg_right (by linarith)
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
  · intro u h hu hh
    exact (hi hu hh).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) (torusParabolicSize_nonneg _))
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))

/-- Almost everywhere positivity of the distances to the centres. -/
theorem ae_ae_chain_pos (z z' u u' : SpaceTime) :
    ∀ᵐ w : SpaceTime ∂volume, (0 < torusParabolicSize (z - w) ∧ 0 < torusParabolicSize (0 - w) ∧
        0 < torusParabolicSize (u - w)) ∧ ∀ᵐ v : SpaceTime ∂volume,
      (0 < torusParabolicSize (z' - v) ∧ 0 < torusParabolicSize (0 - v) ∧
        0 < torusParabolicSize (u' - v)) ∧ 0 < torusParabolicSize (w - v) := by
  filter_upwards [ae_torusParabolicSize_sub_pos z, ae_torusParabolicSize_sub_pos 0,
    ae_torusParabolicSize_sub_pos u] with w a b c
  refine ⟨⟨a, b, c⟩, ?_⟩
  filter_upwards [ae_torusParabolicSize_sub_pos z', ae_torusParabolicSize_sub_pos 0,
    ae_torusParabolicSize_sub_pos u', ae_torusParabolicSize_sub_pos w] with v a' b' c' d'
  exact ⟨⟨a', b', c'⟩, d'⟩

end RegularityStructures.Phi43

end
