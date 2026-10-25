/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HolderBesovPeriodisedL1
public import Mathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Uniform L1 bounds for periodic Schwartz multipliers

Poisson summation identifies the periodic multiplier with coefficients `m(k/a)` with the
normalised periodisation of the rescaled inverse Fourier transform of `m`. Its L1 norm is
therefore bounded independently of the frequency scale `a > 0`.

This supplies the one-dimensional multiplier-kernel ingredient in the comparison of the heat and
Littlewood--Paley norms. The Fourier-multiplier argument is standard; Mathlib's Schwartz Poisson
formula discharges the periodisation identity, rather than assuming a multiplier estimate.
-/

public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform SchwartzMap

namespace RegularityStructures

theorem fourier_normalized_dilate (f : ℝ → ℂ) {a : ℝ} (ha : 0 < a) (w : ℝ) :
    𝓕 (fun x : ℝ => a • f (a * x)) w = 𝓕 f (w / a) := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  let g : ℝ → ℂ := fun u => Real.fourierChar (-(u * (w / a))) • f u
  have he (x : ℝ) : Real.fourierChar (-(x * w)) • (a • f (a * x)) = a • g (a * x) := by
    have hp : -((a * x) * (w / a)) = -(x * w) := by field_simp
    unfold g
    rw [hp]
    exact smul_comm _ _ _
  simp_rw [he]
  rw [integral_smul, Measure.integral_comp_mul_left, smul_smul, abs_inv, abs_of_pos ha,
    mul_inv_cancel₀ ha.ne', one_smul]

private def normalizedSchwartzDilate (f : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 0 < a) : 𝓢(ℝ, ℂ) :=
  a • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearEquiv.smulOfNeZero ℝ ℝ a ha.ne').toContinuousLinearEquiv f

private theorem normalizedSchwartzDilate_apply (f : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 0 < a) (x : ℝ) :
    normalizedSchwartzDilate f a ha x = a • f (a * x) := rfl

theorem summable_schwartz_dilated_int (m : 𝓢(ℝ, ℂ)) {a : ℝ} (ha : 0 < a) :
    Summable (fun k : ℤ => m ((k : ℝ) / a)) := by
  let g : 𝓢(ℝ, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearEquiv.smulOfNeZero ℝ ℝ a⁻¹ (inv_ne_zero ha.ne')).toContinuousLinearEquiv m
  have hg : Summable (fun k : ℤ => g (k : ℝ)) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      ((g.isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)
  change Summable (fun k : ℤ => m (a⁻¹ * (k : ℝ))) at hg
  simpa only [div_eq_mul_inv, mul_comm] using hg

theorem continuous_schwartz_multiplier_circle (m : 𝓢(ℝ, ℂ)) {a : ℝ} (ha : 0 < a) :
    Continuous (fun x : UnitAddCircle =>
      ∑' k : ℤ, m ((k : ℝ) / a) * fourier k x) := by
  let F : ℤ → C(UnitAddCircle, ℂ) := fun k => m ((k : ℝ) / a) • fourier k
  have hsum : Summable F := by
    apply Summable.of_norm
    have h := (summable_schwartz_dilated_int m ha).norm
    simpa only [F, norm_smul, fourier_norm, mul_one] using h
  apply (∑' k : ℤ, F k).continuous.congr
  intro x
  rw [← ContinuousMap.tsum_apply hsum]
  exact tsum_congr fun _ => rfl

theorem schwartz_multiplier_kernel_eq_periodise (m : 𝓢(ℝ, ℂ)) {a : ℝ} (ha : 0 < a)
    (x : ℝ) :
    (∑' k : ℤ, m ((k : ℝ) / a) * fourier k (x : UnitAddCircle)) =
      ∑' k : ℤ, a • (𝓕⁻ m : 𝓢(ℝ, ℂ)) (a * (x + k)) := by
  let f : 𝓢(ℝ, ℂ) := normalizedSchwartzDilate (𝓕⁻ m) a ha
  have he (k : ℤ) : 𝓕 f (k : ℝ) = m ((k : ℝ) / a) := by
    rw [SchwartzMap.fourier_coe]
    change 𝓕 (fun x : ℝ => a • (𝓕⁻ m : 𝓢(ℝ, ℂ)) (a * x) : ℝ → ℂ) (k : ℝ) = _
    rw [fourier_normalized_dilate _ ha]
    change (𝓕 (𝓕⁻ m : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ)) ((k : ℝ) / a) = _
    rw [FourierTransform.fourier_fourierInv_eq]
  have hp := f.tsum_eq_tsum_fourier x
  simp_rw [he] at hp
  simpa only [f, normalizedSchwartzDilate_apply] using hp.symm

theorem lintegral_schwartz_multiplier_kernel_le (m : 𝓢(ℝ, ℂ)) {a : ℝ} (ha : 0 < a) :
    (∫⁻ x in Ioc (0 : ℝ) 1,
      ‖∑' k : ℤ, m ((k : ℝ) / a) * fourier k (x : UnitAddCircle)‖ₑ) ≤
        ∫⁻ y : ℝ, ‖(𝓕⁻ m : 𝓢(ℝ, ℂ)) y‖ₑ := by
  simp_rw [schwartz_multiplier_kernel_eq_periodise m ha]
  exact lintegral_scaled_periodise_int_enorm_le
    (fun y => (𝓕⁻ m : 𝓢(ℝ, ℂ)) y) (𝓕⁻ m : 𝓢(ℝ, ℂ)).continuous ha

theorem lintegral_schwartz_multiplier_circle_le (m : 𝓢(ℝ, ℂ)) {a : ℝ} (ha : 0 < a) :
    (∫⁻ x : UnitAddCircle,
      ‖∑' k : ℤ, m ((k : ℝ) / a) * fourier k x‖ₑ) ≤
        ∫⁻ y : ℝ, ‖(𝓕⁻ m : 𝓢(ℝ, ℂ)) y‖ₑ := by
  rw [← UnitAddCircle.lintegral_preimage 0]
  simpa only [zero_add] using lintegral_schwartz_multiplier_kernel_le m ha

end RegularityStructures

end
