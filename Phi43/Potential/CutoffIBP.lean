/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Integration by parts against a monotone cutoff

If `g` is continuous, `h` is smooth and nondecreasing on `[a, s]` with `h a = 0`, `h s = 1`, and
`|∫_r^s g| ≤ M` for all `r ∈ [a, s]`, then `|∫_a^s h g| ≤ M` (`abs_integral_cutoff_le`).  Indeed
`∫_a^s h g = ∫_a^s h' Φ` with `Φ(r) = ∫_r^s g`, and `∫_a^s h' = 1`.
-/

open scoped ContDiff

public section

open MeasureTheory Set intervalIntegral

namespace RegularityStructures.Potential

theorem hasDerivAt_integral_right {g : ℝ → ℝ} (hg : Continuous g) (s r : ℝ) :
    HasDerivAt (fun r => ∫ t in r..s, g t) (-g r) r :=
  integral_hasDerivAt_left (hg.intervalIntegrable _ _)
    (hg.stronglyMeasurableAtFilter _ _) hg.continuousAt

theorem continuous_integral_right {g : ℝ → ℝ} (hg : Continuous g) (s : ℝ) :
    Continuous fun r => ∫ t in r..s, g t :=
  continuous_iff_continuousAt.2 fun r => (hasDerivAt_integral_right hg s r).continuousAt

theorem integral_cutoff_mul_eq {a s : ℝ} {g h : ℝ → ℝ} (hg : Continuous g)
    (hh : ContDiff ℝ 1 h) (hha : h a = 0) :
    ∫ r in a..s, h r * g r = ∫ r in a..s, deriv h r * ∫ t in r..s, g t := by
  have hΦ : ∀ r, HasDerivAt (fun r => ∫ t in r..s, g t) (-g r) r :=
    hasDerivAt_integral_right hg s
  have hhd : ∀ r, HasDerivAt h (deriv h r) r := fun r =>
    ((hh.differentiable (by simp)) r).hasDerivAt
  have key := integral_mul_deriv_eq_deriv_mul_of_hasDerivAt (a := a) (b := s) (u := h)
    (v := fun r => ∫ t in r..s, g t) (u' := deriv h) (v' := fun r => -g r)
    (fun r _ => (hhd r).continuousAt.continuousWithinAt)
    (fun r _ => (hΦ r).continuousAt.continuousWithinAt) (fun r _ => hhd r) (fun r _ => hΦ r)
    ((hh.continuous_deriv (by simp)).intervalIntegrable _ _) (hg.neg.intervalIntegrable _ _)
  simp only [mul_neg, intervalIntegral.integral_neg, integral_same, mul_zero, hha, zero_mul, sub_zero,
    zero_sub] at key
  linarith

theorem abs_integral_cutoff_le {a s : ℝ} (has : a ≤ s) {g h : ℝ → ℝ} (hg : Continuous g)
    (hh : ContDiff ℝ 1 h) (hha : h a = 0) (hhs : h s = 1) (hmono : Monotone h) {M : ℝ}
    (hM : ∀ r ∈ Icc a s, |∫ t in r..s, g t| ≤ M) :
    |∫ r in a..s, h r * g r| ≤ M := by
  rw [integral_cutoff_mul_eq hg hh hha]
  have hd : ∀ r, 0 ≤ deriv h r := fun r => hmono.deriv_nonneg
  have hint : ∫ r in a..s, deriv h r = 1 := by
    rw [integral_deriv_eq_sub (fun r _ => ((hh.differentiable (by simp)) r))
      ((hh.continuous_deriv (by simp)).intervalIntegrable _ _), hha, hhs]
    norm_num
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM a ⟨le_rfl, has⟩)
  calc |∫ r in a..s, deriv h r * ∫ t in r..s, g t|
      ≤ ∫ r in a..s, |deriv h r * ∫ t in r..s, g t| := abs_integral_le_integral_abs has
    _ ≤ ∫ r in a..s, deriv h r * M := by
        refine integral_mono_on has ?_ ?_ fun r hr => ?_
        · exact (((hh.continuous_deriv (by simp)).mul (continuous_integral_right hg s)).abs).intervalIntegrable _ _
        · exact ((hh.continuous_deriv (by simp)).mul continuous_const).intervalIntegrable _ _
        · rw [abs_mul, abs_of_nonneg (hd r)]
          exact mul_le_mul_of_nonneg_left (hM r hr) (hd r)
    _ = M := by rw [intervalIntegral.integral_mul_const, hint, one_mul]

end RegularityStructures.Potential

end
