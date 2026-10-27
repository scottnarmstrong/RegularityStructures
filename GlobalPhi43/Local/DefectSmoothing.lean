/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.SchauderInputs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! The actual positive normalized-kernel estimate for the smooth defects.
The kernel is represented by a probability measure, allowing later attachment
to MW20's limiting kernel without changing the past-looking convention.
No defect derivative or defect Hölder bound is used. -/
public section

namespace GlobalPhi43.Local

open MeasureTheory

/-- The complete signed forcing from the local expansion is bounded by sup norms. -/
theorem signed_defect_bound {e₁ e₂ e₃ v E₁ E₂ E₃ M : ℝ}
    (h₁ : |e₁| ≤ E₁) (h₂ : |e₂| ≤ E₂) (h₃ : |e₃| ≤ E₃)
    (hv : |v| ≤ M) (hE₂ : 0 ≤ E₂) :
    |-e₁ + e₃ + 3 * v * e₂| ≤ E₁ + E₃ + 3 * M * E₂ := by
  calc
    _ ≤ |-e₁ + e₃| + |3 * v * e₂| := abs_add_le _ _
    _ ≤ |e₁| + |e₃| + 3 * |v| * |e₂| := by
      have h := abs_add_le (-e₁) e₃
      simpa [abs_mul] using add_le_add_right h |3 * v * e₂|
    _ ≤ E₁ + E₃ + 3 * |v| * E₂ :=
      add_le_add (add_le_add h₁ h₃)
        (mul_le_mul_of_nonneg_left h₂ (by positivity))
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hv hE₂]

/-- Averaging the signed defect forcing against any positive mass-one kernel.
For past smoothing, instantiate each eᵢ here with z ↦ eᵢ(x+z). -/
theorem defect_average_bound {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ]
    (e₁ e₂ e₃ : E → ℝ) {v E₁ E₂ E₃ M : ℝ}
    (h₁ : ∀ᵐ z ∂μ, |e₁ z| ≤ E₁) (h₂ : ∀ᵐ z ∂μ, |e₂ z| ≤ E₂)
    (h₃ : ∀ᵐ z ∂μ, |e₃ z| ≤ E₃) (hv : |v| ≤ M) (hE₂ : 0 ≤ E₂) :
    |∫ z, -e₁ z + e₃ z + 3 * v * e₂ z ∂μ| ≤ E₁ + E₃ + 3 * M * E₂ := by
  have hbound : ∀ᵐ z ∂μ, ‖-e₁ z + e₃ z + 3 * v * e₂ z‖ ≤
      E₁ + E₃ + 3 * M * E₂ := by
    filter_upwards [h₁, h₂, h₃] with z hz₁ hz₂ hz₃
    exact signed_defect_bound hz₁ hz₂ hz₃ hv hE₂
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const hbound

end GlobalPhi43.Local
