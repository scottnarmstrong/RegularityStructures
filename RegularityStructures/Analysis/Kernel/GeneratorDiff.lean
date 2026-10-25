/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Kernel.GeneratorStep
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiating `v ↦ ∫ q_v(z - y) φ(y) dy` under the integral sign

For `v > 0` and `φ` continuous with compact support, `F(v) = ∫ q_v(z - y) φ(y) dy` has derivative
`∫ (∂_v q_v)(z - y) φ(y) dy`. The domination uses the time-derivative bound of
`RegularityStructures.Analysis.Kernel.TimeDeriv` and boundedness of the profile.
-/

public section

open MeasureTheory Filter Topology Real
open scoped ContDiff

namespace RegularityStructures

theorem continuous_parabolicTimeDeriv {v : ℝ} (hv : 0 < v) : Continuous (parabolicTimeDeriv v) := by
  have hq := contDiff_parabolicKernel hv
  have e : parabolicTimeDeriv v = fun w => generatorTimeCoeff *
      (dirDeriv timeDir)^[2] (parabolicKernel v) w -
        generatorSpaceCoeff * ∑ i : Fin 3, (dirDeriv (spaceDir i))^[4] (parabolicKernel v) w :=
    funext (parabolicTimeDeriv_eq hv)
  rw [e]
  exact (continuous_const.mul (contDiff_iterate_dirDeriv hq _ 2).continuous).sub
    (continuous_const.mul (continuous_finsetSum _ fun i _ =>
      (contDiff_iterate_dirDeriv hq _ 4).continuous))

theorem exists_parabolicTimeProfile_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ w, parabolicTimeProfile w ≤ C := by
  obtain ⟨C, hC⟩ := parabolicTimeProfile_decay 0
  refine ⟨max C 0, le_max_right _ _, fun w => ?_⟩
  have := hC w
  simp only [Nat.cast_zero, neg_zero, Real.rpow_zero, Finset.prod_const_one, mul_one] at this
  exact this.trans (le_max_left _ _)

/-- A uniform bound of `∂_x q_x` for `x ≥ v/2`. -/
theorem exists_abs_parabolicTimeDeriv_le {v : ℝ} (hv : 0 < v) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, v / 2 < x → ∀ w, |parabolicTimeDeriv x w| ≤ B := by
  obtain ⟨C, hC0, hC⟩ := exists_parabolicTimeProfile_le
  have hv2 : 0 < v / 2 := half_pos hv
  refine ⟨(v / 2)⁻¹ * (v / 2) ^ (-(5 / 4 : ℝ)) * C, ?_, fun x hx w => ?_⟩
  · exact mul_nonneg (mul_nonneg (inv_nonneg.2 hv2.le) (Real.rpow_nonneg hv2.le _)) hC0
  · have hx0 : 0 < x := hv2.trans hx
    refine (abs_parabolicTimeDeriv_le hx0 w).trans ?_
    have h1 : x⁻¹ ≤ (v / 2)⁻¹ := inv_anti₀ hv2 hx.le
    have h2 : x ^ (-(5 / 4 : ℝ)) ≤ (v / 2) ^ (-(5 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hv2 hx.le (by norm_num)
    have h3 := hC (parabolicDilate (x ^ (-(1 / 4 : ℝ))) w)
    have hG : 0 ≤ parabolicTimeProfile (parabolicDilate (x ^ (-(1 / 4 : ℝ))) w) := by
      unfold parabolicTimeProfile
      positivity
    exact mul_le_mul (mul_le_mul h1 h2 (Real.rpow_nonneg hx0.le _) (inv_nonneg.2 hv2.le)) h3 hG
      (mul_nonneg (inv_nonneg.2 hv2.le) (Real.rpow_nonneg hv2.le _))

variable {φ : ParabolicSpace → ℝ}

theorem hasDerivAt_apply_parabolicSemigroup {v : ℝ} (hv : 0 < v) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (z : ParabolicSpace) :
    HasDerivAt (fun x => ∫ y, parabolicKernel x (z - y) * φ y)
      (∫ y, parabolicTimeDeriv v (z - y) * φ y) v := by
  obtain ⟨B, hB0, hB⟩ := exists_abs_parabolicTimeDeriv_le hv
  have hsub : Continuous fun y : ParabolicSpace => z - y := continuous_const.sub continuous_id
  have hmeas : ∀ x, AEStronglyMeasurable (fun y => parabolicKernel x (z - y) * φ y) volume :=
    fun x => (((measurable_parabolicKernel x).comp (measurable_const.sub measurable_id)).mul
      hφ.measurable).aestronglyMeasurable
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := v)
    (s := Set.Ioi (v / 2)) (Ioi_mem_nhds (half_lt_self hv))
    (F := fun x y => parabolicKernel x (z - y) * φ y)
    (F' := fun x y => parabolicTimeDeriv x (z - y) * φ y)
    (bound := fun y => B * |φ y|)
    (Filter.Eventually.of_forall hmeas)
    (((contDiff_parabolicKernel hv).continuous.comp hsub).mul hφ
      |>.integrable_of_hasCompactSupport hc.mul_left)
    (((continuous_parabolicTimeDeriv hv).comp hsub).mul hφ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y x hx => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hB x hx _) (abs_nonneg _))
    ((hφ.norm.integrable_of_hasCompactSupport hc.norm).const_mul B)
    (Filter.Eventually.of_forall fun y x hx =>
      (hasDerivAt_parabolicKernel_time (hx.trans' (half_pos hv)) (z - y)).mul_const (φ y))
  exact key.2

end RegularityStructures

end
