/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Kernel.GeneratorLip

/-!
# Convergence and boundedness of `Q_v φ`

* `abs_apply_sub_le`: `|Q_v φ(z) - φ(z)| ≤ C v^{1/4}`;
* `abs_apply_le`: `|Q_v g(z)| ≤ M₀ sup|g|`.
-/

public section

open MeasureTheory Filter Topology Real
open scoped ContDiff

namespace RegularityStructures

theorem apply_parabolicSemigroup (v : ℝ) (g : ParabolicSpace → ℝ) (z : ParabolicSpace) :
    parabolicSemigroup.apply v g z = ∫ y, parabolicKernel v (z - y) * g y := rfl

theorem integrable_abs_kernel_mul_norm_rpow {v : ℝ} (hv : 0 < v) {r : ℝ} (hr : 0 ≤ r)
    (z : ParabolicSpace) :
    Integrable fun y => |parabolicKernel v (z - y)| * parabolicNorm (y - z) ^ r :=
  parabolicSemigroup.integrable_moment hv hr z

theorem integral_abs_kernel_mul_norm_rpow_le {v : ℝ} (hv : 0 < v) {r : ℝ} (hr : 0 ≤ r)
    (z : ParabolicSpace) :
    ∫ y, |parabolicKernel v (z - y)| * parabolicNorm (y - z) ^ r ≤
      parabolicMomentConst r * v ^ (r / 4) :=
  parabolicSemigroup.moment_le hv hr z

theorem abs_apply_sub_le {φ : ParabolicSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ∃ C : ℝ, ∀ v : ℝ, 0 < v → ∀ z, |parabolicSemigroup.apply v φ z - φ z| ≤ C * v ^ (1 / 4 : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_sub_le_parabolicNorm hφ hc
  refine ⟨C * parabolicMomentConst 1, fun v hv z => ?_⟩
  have hq := integrable_parabolicKernel_sub hv z
  have hφi : Integrable fun y => parabolicKernel v (z - y) * φ y :=
    (((contDiff_parabolicKernel hv).continuous.comp
      (continuous_const.sub continuous_id)).mul hφ.continuous).integrable_of_hasCompactSupport
      hc.mul_left
  have e : parabolicSemigroup.apply v φ z - φ z =
      ∫ y, parabolicKernel v (z - y) * (φ y - φ z) := by
    simp_rw [mul_sub]
    rw [integral_sub hφi (hq.mul_const _), integral_mul_const, integral_parabolicKernel_sub hv z,
      one_mul]
    rfl
  rw [e]
  have hmom := integrable_abs_kernel_mul_norm_rpow hv zero_le_one z
  have hm1 := integral_abs_kernel_mul_norm_rpow_le hv zero_le_one z
  calc |∫ y, parabolicKernel v (z - y) * (φ y - φ z)|
      = ‖∫ y, parabolicKernel v (z - y) * (φ y - φ z)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ y, C * (|parabolicKernel v (z - y)| * parabolicNorm (y - z) ^ (1 : ℝ)) := by
        refine norm_integral_le_of_norm_le (hmom.const_mul C) (Filter.Eventually.of_forall fun y => ?_)
        rw [Real.norm_eq_abs, abs_mul, Real.rpow_one]
        have := hC y z
        calc |parabolicKernel v (z - y)| * |φ y - φ z|
            ≤ |parabolicKernel v (z - y)| * (C * parabolicNorm (y - z)) :=
              mul_le_mul_of_nonneg_left this (abs_nonneg _)
          _ = _ := by ring
    _ = C * ∫ y, |parabolicKernel v (z - y)| * parabolicNorm (y - z) ^ (1 : ℝ) :=
        integral_const_mul _ _
    _ ≤ C * (parabolicMomentConst 1 * v ^ (1 / 4 : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hC0
        simpa using hm1
    _ = _ := by ring

theorem abs_apply_le {g : ParabolicSpace → ℝ} {B : ℝ} (hg : ∀ y, |g y| ≤ B) {v : ℝ} (hv : 0 < v)
    (z : ParabolicSpace) :
    |parabolicSemigroup.apply v g z| ≤ parabolicMomentConst 0 * B := by
  have hmom := integrable_abs_kernel_mul_norm_rpow hv le_rfl z
  have hm0 := integral_abs_kernel_mul_norm_rpow_le hv le_rfl z
  have hB : 0 ≤ B := (abs_nonneg _).trans (hg z)
  simp only [Real.rpow_zero, mul_one, zero_div] at hmom hm0
  rw [apply_parabolicSemigroup]
  calc |∫ y, parabolicKernel v (z - y) * g y|
      = ‖∫ y, parabolicKernel v (z - y) * g y‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ y, |parabolicKernel v (z - y)| * B := by
        refine norm_integral_le_of_norm_le (hmom.mul_const B) (Filter.Eventually.of_forall fun y => ?_)
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (hg y) (abs_nonneg _)
    _ = (∫ y, |parabolicKernel v (z - y)|) * B := integral_mul_const _ _
    _ ≤ parabolicMomentConst 0 * B := by
        refine mul_le_mul_of_nonneg_right ?_ hB
        simpa using hm0

end RegularityStructures

end
