/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.SpaceTimeMeasure
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Weighted square estimate for signed averaging kernels

The total variation of an averaging kernel controls its action on a square-integrable
function. The proof integrates a nonnegative weighted square and applies the quadratic
discriminant criterion, so it does not require the averaging kernel to be nonnegative.
-/

public noncomputable section

open MeasureTheory Real

namespace RegularityStructures.Phi43

theorem integral_mul_sq_le_abs_mass
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f p : α → ℝ}
    (hp : Integrable p μ) (hfp : Integrable (fun v => f v * p v) μ)
    (hf2p : Integrable (fun v => f v ^ 2 * |p v|) μ) :
    (∫ v, f v * p v ∂μ) ^ 2 ≤
      (∫ v, |p v| ∂μ) * ∫ v, f v ^ 2 * |p v| ∂μ := by
  let N : ℝ := ∫ v, |p v| ∂μ
  let J : ℝ := ∫ v, |f v| * |p v| ∂μ
  let I : ℝ := ∫ v, f v ^ 2 * |p v| ∂μ
  have hpabs : Integrable (fun v => |p v|) μ := hp.norm
  have hprodabs : Integrable (fun v => |f v| * |p v|) μ := by
    apply hfp.norm.congr
    filter_upwards [] with v
    rw [Real.norm_eq_abs, abs_mul]
  have hpoly : ∀ c : ℝ, 0 ≤ N * (c * c) + (-2 * J) * c + I := by
    intro c
    let Q : α → ℝ := fun v =>
      f v ^ 2 * |p v| - 2 * c * (|f v| * |p v|) + c ^ 2 * |p v|
    have hQnonneg : ∀ v, 0 ≤ Q v := by
      intro v
      have h := mul_nonneg (sq_nonneg (|f v| - c)) (abs_nonneg (p v))
      have heq : Q v = (|f v| - c) ^ 2 * |p v| := by
        dsimp [Q]
        rw [← sq_abs (f v)]
        ring
      rw [heq]
      exact h
    have hint : 0 ≤ ∫ v, Q v ∂μ := integral_nonneg hQnonneg
    have heq : (∫ v, Q v ∂μ) = N * (c * c) + (-2 * J) * c + I := by
      dsimp [Q]
      rw [integral_add (f := fun v => f v ^ 2 * |p v| - 2 * c * (|f v| * |p v|))
          (hf2p.sub (hprodabs.const_mul (2 * c)))
          (hpabs.const_mul (c ^ 2)),
        integral_sub hf2p (hprodabs.const_mul (2 * c)),
        integral_const_mul, integral_const_mul]
      dsimp [N, J, I]
      ring
    rw [heq] at hint
    exact hint
  have hdisc := discrim_le_zero hpoly
  simp only [discrim] at hdisc
  have hJI : J ^ 2 ≤ N * I := by nlinarith only [hdisc]
  have hJ : 0 ≤ J := integral_nonneg fun v => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have habs : |∫ v, f v * p v ∂μ| ≤ J := by
    simpa only [Real.norm_eq_abs, abs_mul] using
      norm_integral_le_integral_norm (f := fun v => f v * p v) (μ := μ)
  have hsq : (∫ v, f v * p v ∂μ) ^ 2 ≤ J ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg _) hJ).mpr habs
    simpa only [sq_abs] using h
  exact hsq.trans hJI

end RegularityStructures.Phi43

end
