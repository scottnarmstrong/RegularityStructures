/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.KernelBoundsGlobal

/-!
# The cancelled massive heat kernel

The factor `exp (-t) - 1` removes one parabolic order from the massive heat kernel.  This is
the elementary order-one part of the remainder `G - K` in the constants comparison.
-/

@[expose] public noncomputable section

open Real

namespace RegularityStructures.Phi43

private theorem constantsComparison_torusParabolicSize_time_le_sq_factor (z : SpaceTime) :
    |z.1| ≤ torusParabolicSize z ^ 2 := by
  have hs := Real.sq_sqrt (abs_nonneg z.1)
  have hroot : 0 ≤ √|z.1| := Real.sqrt_nonneg _
  have hsp : 0 ≤ torusSpatialNorm z.2 := torusSpatialNorm_nonneg z.2
  unfold torusParabolicSize at hs ⊢
  nlinarith [sq_nonneg (torusSpatialNorm z.2), mul_nonneg hroot hsp]

private theorem constantsComparison_exp_sub_one_abs_le_time {t : ℝ} (ht : 0 < t) :
    |Real.exp (-t) - 1| ≤ t := by
  have hexp : Real.exp (-t) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  rw [abs_of_nonpos]
  · linarith [Real.add_one_le_exp (-t)]
  · linarith

theorem constantsComparison_massive_factor_order_one :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : SpaceTime, 0 < torusParabolicSize z →
      |(Real.exp (-z.1) - 1) * massiveHeatKernel z| ≤
        C * torusParabolicSize z ^ (-(1 : ℝ)) := by
  obtain ⟨C, hC, hG⟩ := massiveHeatKernel_global_singular_bound
  refine ⟨C, hC, ?_⟩
  intro z hz
  by_cases ht : z.1 ≤ 0
  · have hzero : massiveHeatKernel z = 0 := by
      simp [massiveHeatKernel, not_lt.mpr ht]
    rw [hzero, mul_zero, abs_zero]
    exact mul_nonneg hC (Real.rpow_nonneg hz.le _)
  · have htpos : 0 < z.1 := lt_of_not_ge ht
    have hspos : 0 < torusParabolicSize z := hz
    have htime : z.1 ≤ torusParabolicSize z ^ (2 : ℕ) := by
      have hsq := constantsComparison_torusParabolicSize_time_le_sq_factor z
      rw [abs_of_pos htpos] at hsq
      exact hsq
    have hcancel := constantsComparison_exp_sub_one_abs_le_time htpos
    have hGbound := hG z hz
    have hstep₁ :
        |Real.exp (-z.1) - 1| * massiveHeatKernel z ≤
          z.1 * massiveHeatKernel z := by
      exact mul_le_mul_of_nonneg_right hcancel (massiveHeatKernel_nonneg z)
    have hstep₂ : z.1 * massiveHeatKernel z ≤
        z.1 * (C * torusParabolicSize z ^ (-(3 : ℝ))) := by
      exact mul_le_mul_of_nonneg_left hGbound (le_of_lt htpos)
    have hpow : torusParabolicSize z ^ (2 : ℕ) *
        torusParabolicSize z ^ (-(3 : ℝ)) =
        torusParabolicSize z ^ (-(1 : ℝ)) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_add hspos]
      norm_num
    have hstep₃ : z.1 * (C * torusParabolicSize z ^ (-(3 : ℝ))) ≤
        C * torusParabolicSize z ^ (-(1 : ℝ)) := by
      calc
        z.1 * (C * torusParabolicSize z ^ (-(3 : ℝ))) =
            C * (z.1 * torusParabolicSize z ^ (-(3 : ℝ))) := by ring
        _ ≤ C * (torusParabolicSize z ^ (2 : ℕ) *
            torusParabolicSize z ^ (-(3 : ℝ))) := by
          gcongr
        _ = C * torusParabolicSize z ^ (-(1 : ℝ)) := by rw [hpow]
    calc
      |(Real.exp (-z.1) - 1) * massiveHeatKernel z| =
          |Real.exp (-z.1) - 1| * massiveHeatKernel z := by
            rw [abs_mul, abs_of_nonneg (massiveHeatKernel_nonneg z)]
      _ ≤ z.1 * massiveHeatKernel z := hstep₁
      _ ≤ z.1 * (C * torusParabolicSize z ^ (-(3 : ℝ))) := hstep₂
      _ ≤ C * torusParabolicSize z ^ (-(1 : ℝ)) := hstep₃

end RegularityStructures.Phi43

end
