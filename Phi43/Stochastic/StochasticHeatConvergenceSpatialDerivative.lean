/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.KernelBoundsSpatialSingularDerivative
public import RegularityStructures.Torus.KernelBoundsLargeTime

/-!
# Spatial derivatives controlled by a wider Gaussian

The first Gaussian derivative is bounded by a multiple of the Gaussian at twice the time.
Periodisation preserves this bound, yielding control at all times rather than only near the
space-time origin. This is a spatial translation input for the space-time increment bound; compare
[Hai14, (5.3)].
-/

@[expose] public noncomputable section

open MeasureTheory Real Set

namespace RegularityStructures.Phi43

private theorem derivative_coefficient_nonneg {t : ℝ} (ht : 0 < t) :
    0 ≤ firstSpatialDerivativeCoefficient t := by
  unfold firstSpatialDerivativeCoefficient
  exact mul_nonneg (rpow_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) pi_pos.le) ht.le) _) (mul_nonneg
    (mul_nonneg (by norm_num) (sqrt_nonneg _)) gaussianExpDerivativeBaseBound_nonneg)

theorem gaussKernelSpaceLine_first_deriv_dilation
    {t : ℝ} (ht : 0 < t) (i : Fin 3) (y : Fin 3 → ℝ) (k : Fin 3 → ℤ) :
    |iteratedDeriv 1 (gaussKernelSpaceLine t i y k) (y i)| ≤
      firstSpatialDerivativeCoefficient t *
        ((4 * π * (2 * t)) ^ (-(3 : ℝ) / 2))⁻¹ *
          gaussKernel (2 * t) (y + fun j => (k j : ℝ)) := by
  let a : ℝ := (4 * t)⁻¹
  let b : ℝ := a / 2
  let q : Fin 3 → ℝ := fun j => y j + (k j : ℝ)
  have ha : 0 < a := inv_pos.mpr (mul_pos (by norm_num) ht)
  have hpref : 0 ≤ (4 * π * t) ^ (-(3 : ℝ) / 2) :=
    rpow_nonneg (mul_nonneg (mul_nonneg (by norm_num) pi_pos.le) ht.le) _
  have hD : 0 ≤ 2 * √(2 * a) * gaussianExpDerivativeBaseBound :=
    mul_nonneg (mul_nonneg (by norm_num) (sqrt_nonneg _)) gaussianExpDerivativeBaseBound_nonneg
  have hprod :
      (∏ j : Fin 3, if j = i then 1 else exp (-a * (q j) ^ 2)) ≤
        ∏ j : Fin 3, if j = i then 1 else exp (-b * (q j) ^ 2) := by
    apply Finset.prod_le_prod₀
    · intro j _
      split_ifs
      · exact zero_le_one
      · exact exp_nonneg _
    · intro j _
      split_ifs with hji
      · exact le_rfl
      · apply exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right (by dsimp [b]; linarith only [ha]) (sq_nonneg _)
  have hC : 0 ≤ gaussKernelSpaceLineCoeff t i y k := by
    unfold gaussKernelSpaceLineCoeff
    apply mul_nonneg hpref
    apply Finset.prod_nonneg
    intro j _
    split_ifs
    · exact zero_le_one
    · exact exp_nonneg _
  have hCbound : gaussKernelSpaceLineCoeff t i y k ≤
      (4 * π * t) ^ (-(3 : ℝ) / 2) *
        ∏ j : Fin 3, if j = i then 1 else exp (-b * (q j) ^ 2) :=
    mul_le_mul_of_nonneg_left hprod hpref
  have hprodeq :
      (∏ j : Fin 3, if j = i then 1 else exp (-b * (q j) ^ 2)) *
        exp (-b * (q i) ^ 2) = ∏ j : Fin 3, exp (-b * (q j) ^ 2) := by
    fin_cases i <;> norm_num [Fin.prod_univ_three] <;> ring
  have hraw : |iteratedDeriv 1 (gaussKernelSpaceLine t i y k) (y i)| ≤
      firstSpatialDerivativeCoefficient t * ∏ j : Fin 3, exp (-b * (q j) ^ 2) := by
    rw [iteratedDeriv_gaussKernelSpaceLine, abs_mul, abs_of_nonneg hC]
    calc
      _ ≤ gaussKernelSpaceLineCoeff t i y k *
          ((2 * √(2 * a) * gaussianExpDerivativeBaseBound) * exp (-b * (q i) ^ 2)) :=
        mul_le_mul_of_nonneg_left (gaussian_expPowFun_one_deriv_center_bound ha (q i)) hC
      _ ≤ ((4 * π * t) ^ (-(3 : ℝ) / 2) *
          ∏ j : Fin 3, if j = i then 1 else exp (-b * (q j) ^ 2)) *
            ((2 * √(2 * a) * gaussianExpDerivativeBaseBound) * exp (-b * (q i) ^ 2)) :=
        mul_le_mul_of_nonneg_right hCbound (mul_nonneg hD (exp_nonneg _))
      _ = firstSpatialDerivativeCoefficient t * ∏ j : Fin 3, exp (-b * (q j) ^ 2) := by
        rw [show ((4 * π * t) ^ (-(3 : ℝ) / 2) *
            ∏ j : Fin 3, if j = i then 1 else exp (-b * (q j) ^ 2)) *
              ((2 * √(2 * a) * gaussianExpDerivativeBaseBound) * exp (-b * (q i) ^ 2)) =
            firstSpatialDerivativeCoefficient t *
              ((∏ j : Fin 3, if j = i then 1 else exp (-b * (q j) ^ 2)) *
                exp (-b * (q i) ^ 2)) by dsimp [firstSpatialDerivativeCoefficient, a]; ring]
        rw [hprodeq]
  have hb : b = (4 * (2 * t))⁻¹ := by
    dsimp [b, a]
    field_simp
  have hbase : 0 < 4 * π * (2 * t) :=
    mul_pos (mul_pos (by norm_num) pi_pos) (mul_pos (by norm_num) ht)
  have hprefne : (4 * π * (2 * t)) ^ (-(3 : ℝ) / 2) ≠ 0 :=
    (rpow_pos_of_pos hbase _).ne'
  have htarget : firstSpatialDerivativeCoefficient t *
      ((4 * π * (2 * t)) ^ (-(3 : ℝ) / 2))⁻¹ *
        gaussKernel (2 * t) (y + fun j => (k j : ℝ)) =
      firstSpatialDerivativeCoefficient t * ∏ j : Fin 3, exp (-b * (q j) ^ 2) := by
    rw [gaussKernel_eq_prod]
    simp only [Pi.add_apply, hb, q]
    field_simp
  exact hraw.trans_eq htarget.symm

theorem heatKernelLift_first_deriv_dilation
    {t : ℝ} (ht : 0 < t) (i : Fin 3) (y : Fin 3 → ℝ)
    (hy : ∀ j, y j ∈ Icc (-1 / 2 : ℝ) (1 / 2)) :
    |gaussKernelSpaceLine_first_deriv_tsum t i y| ≤
      (firstSpatialDerivativeCoefficient t *
        ((4 * π * (2 * t)) ^ (-(3 : ℝ) / 2))⁻¹) * heatKernelLift (2 * t) y := by
  have hsum := summable_heatKernelLift_spaceLine_iterated ht i 1 y hy
  have hsumG := summable_heatKernelLift_spaceLine (t := 2 * t)
    (mul_pos (by norm_num) ht) 0 y hy
  simp only [gaussKernelSpaceLine, Function.update_eq_self] at hsumG
  calc
    _ ≤ ∑' k : Fin 3 → ℤ, |iteratedDeriv 1 (gaussKernelSpaceLine t i y k) (y i)| :=
      norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' k : Fin 3 → ℤ,
        (firstSpatialDerivativeCoefficient t * ((4 * π * (2 * t)) ^ (-(3 : ℝ) / 2))⁻¹) *
          gaussKernel (2 * t) (y + fun j => (k j : ℝ)) :=
      hsum.abs.tsum_le_tsum (gaussKernelSpaceLine_first_deriv_dilation ht i y)
        (hsumG.mul_left _)
    _ = _ := by rw [tsum_mul_left]; rfl

theorem heatKernelLift_first_deriv_le_time_factor :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {t : ℝ}, 0 < t → ∀ i : Fin 3, ∀ y : Fin 3 → ℝ,
      (∀ j, y j ∈ Icc (-1 / 2 : ℝ) (1 / 2)) →
      |gaussKernelSpaceLine_first_deriv_tsum t i y| ≤
        C * t ^ (-(1 / 2 : ℝ)) * heatKernelLift (2 * t) y := by
  let C : ℝ := firstSpatialDerivativeCoefficient 1 * (8 * π) ^ (3 / 2 : ℝ)
  have hC : 0 ≤ C := mul_nonneg (derivative_coefficient_nonneg (by norm_num))
    (rpow_nonneg (mul_nonneg (by norm_num) pi_pos.le) _)
  refine ⟨C, hC, ?_⟩
  intro t ht i y hy
  have hcoeff : firstSpatialDerivativeCoefficient t =
      firstSpatialDerivativeCoefficient 1 * t ^ (-(2 : ℝ)) := by
    rw [rpow_neg ht.le, rpow_two, ← div_eq_mul_inv]
    exact (eq_div_iff (pow_ne_zero 2 ht.ne')).mpr (firstSpatialDerivativeCoefficient_mul_sq ht)
  have hbase : 0 ≤ 4 * π * (2 * t) :=
    mul_nonneg (mul_nonneg (by norm_num) pi_pos.le) (mul_nonneg (by norm_num) ht.le)
  have hpref : ((4 * π * (2 * t)) ^ (-(3 : ℝ) / 2))⁻¹ =
      (8 * π) ^ (3 / 2 : ℝ) * t ^ (3 / 2 : ℝ) := by
    rw [← rpow_neg hbase]
    rw [show -(-(3 : ℝ) / 2) = (3 / 2 : ℝ) by ring]
    rw [show 4 * π * (2 * t) = (8 * π) * t by ring]
    exact mul_rpow (mul_nonneg (by norm_num) pi_pos.le) ht.le
  have hcombine : firstSpatialDerivativeCoefficient t *
      ((4 * π * (2 * t)) ^ (-(3 : ℝ) / 2))⁻¹ = C * t ^ (-(1 / 2 : ℝ)) := by
    rw [hcoeff, hpref]
    calc
      _ = C * (t ^ (-(2 : ℝ)) * t ^ (3 / 2 : ℝ)) := by dsimp [C]; ring
      _ = C * t ^ (-(1 / 2 : ℝ)) := by
        rw [← rpow_add ht]
        norm_num
  simpa only [hcombine] using heatKernelLift_first_deriv_dilation ht i y hy

end RegularityStructures.Phi43

end
