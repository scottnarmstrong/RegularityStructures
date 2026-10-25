/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergenceSpatialDerivative

/-!
# A global-in-time spatial derivative bound

The small-time periodised Gaussian estimate and the wider-Gaussian derivative bound combine
into a spatially uniform bound `C * (t⁻² + 1)`. Its massive time tail is integrable and gives
the spatial modulus of the covariance resolvent used for the scale Cauchy estimate.
-/

@[expose] public noncomputable section

open MeasureTheory Real Set

namespace RegularityStructures.Phi43

theorem heatKernelLift_first_deriv_uniform_time_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {t : ℝ}, 0 < t → ∀ i : Fin 3, ∀ y : Fin 3 → ℝ,
      (∀ j, y j ∈ Icc (-1 / 2 : ℝ) (1 / 2)) →
      |gaussKernelSpaceLine_first_deriv_tsum t i y| ≤
        C * (t ^ (-(2 : ℝ)) + 1) := by
  obtain ⟨D, hD, hdilate⟩ := heatKernelLift_first_deriv_le_time_factor
  obtain ⟨L, hlarge⟩ := heatKernel_le_large_time
  let A : ℝ := firstSpatialDerivativeCoefficient 1 * gaussianProductMajorantSum
  let B : ℝ := D * max L 0
  have hcoeff1 : 0 ≤ firstSpatialDerivativeCoefficient 1 := by
    unfold firstSpatialDerivativeCoefficient
    exact mul_nonneg (rpow_nonneg (by linarith only [pi_pos]) _)
      (mul_nonneg (mul_nonneg (by norm_num) (sqrt_nonneg _)) gaussianExpDerivativeBaseBound_nonneg)
  have hA : 0 ≤ A := mul_nonneg hcoeff1 nonneg_gaussianProductMajorantSum
  have hB : 0 ≤ B := mul_nonneg hD (le_max_right _ _)
  refine ⟨A + B, add_nonneg hA hB, ?_⟩
  intro t ht i y hy
  have htimepow : 0 ≤ t ^ (-(2 : ℝ)) := rpow_nonneg ht.le _
  by_cases ht1 : t ≤ 1
  · have hcoefft : 0 ≤ firstSpatialDerivativeCoefficient t := by
      unfold firstSpatialDerivativeCoefficient
      exact mul_nonneg (rpow_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) pi_pos.le) ht.le) _)
        (mul_nonneg (mul_nonneg (by norm_num) (sqrt_nonneg _)) gaussianExpDerivativeBaseBound_nonneg)
    have hscale : 0 ≤ firstSpatialDerivativeScale t :=
      div_nonneg (inv_nonneg.mpr (mul_nonneg (by norm_num) ht.le)) (by norm_num)
    have hexp : exp (-firstSpatialDerivativeScale t * sqNorm3 y) ≤ 1 := by
      apply exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hscale)
        (Finset.sum_nonneg fun j _ => sq_nonneg (y j))
    have hcoeff : firstSpatialDerivativeCoefficient t =
        firstSpatialDerivativeCoefficient 1 * t ^ (-(2 : ℝ)) := by
      rw [rpow_neg ht.le, rpow_two, ← div_eq_mul_inv]
      exact (eq_div_iff (pow_ne_zero 2 ht.ne')).mpr (firstSpatialDerivativeCoefficient_mul_sq ht)
    calc
      _ ≤ firstSpatialDerivativeCoefficient t *
          exp (-firstSpatialDerivativeScale t * sqNorm3 y) * gaussianProductMajorantSum :=
        heatKernelLift_first_spatial_deriv_tsum_bound ht ht1 i y hy
      _ ≤ firstSpatialDerivativeCoefficient t * gaussianProductMajorantSum := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_of_le_one_right hcoefft hexp) nonneg_gaussianProductMajorantSum
      _ = A * t ^ (-(2 : ℝ)) := by rw [hcoeff]; dsimp [A]; ring
      _ ≤ (A + B) * (t ^ (-(2 : ℝ)) + 1) := by
        exact (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB) htimepow).trans
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (add_nonneg hA hB))
  · have ht1' : 1 ≤ t := le_of_not_ge ht1
    have hpow : t ^ (-(1 / 2 : ℝ)) ≤ 1 := by
      simpa only [one_rpow] using rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1)
        ht1' (by norm_num : -(1 / 2 : ℝ) ≤ 0)
    have hheat : heatKernelLift (2 * t) y ≤ max L 0 := by
      rw [← heatKernel_comp_torusProj_eq_lift]
      exact (hlarge (2 * t) (by linarith only [ht1']) _).trans (le_max_left _ _)
    calc
      _ ≤ D * t ^ (-(1 / 2 : ℝ)) * heatKernelLift (2 * t) y := hdilate ht i y hy
      _ ≤ D * t ^ (-(1 / 2 : ℝ)) * max L 0 :=
        mul_le_mul_of_nonneg_left hheat (mul_nonneg hD (rpow_nonneg ht.le _))
      _ ≤ D * max L 0 := by
        exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hD hpow) (le_max_right _ _)
      _ = B := rfl
      _ ≤ (A + B) * (t ^ (-(2 : ℝ)) + 1) := by
        exact (le_add_of_nonneg_left hA).trans
          (le_mul_of_one_le_right (add_nonneg hA hB) (le_add_of_nonneg_left htimepow))

end RegularityStructures.Phi43

end
