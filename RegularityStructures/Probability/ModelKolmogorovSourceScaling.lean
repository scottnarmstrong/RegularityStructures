/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovGlobalSourceMoments

/-!
# Scaling of the source products

The Chen transport terms contain two source factors, each carrying the same constant `C`. The source
bounds give `0 ≤ C ≤ Cbar`; this elementary lemma is the exact algebraic conversion of the resulting
`C^(2*p)` factor to the allowed `Cbar * C` factor. It is used only for nonnegative scale weights.

This is the source-product part of the Pi/Gamma induction in the Kolmogorov criterion for models.
-/

public section

open scoped ENNReal

namespace RegularityStructures

theorem ennreal_two_source_product_le_of_upperBound
    {p : ℕ} {C Cbar a b : ℝ}
    (hC : 0 ≤ C) (hCbar : C ≤ Cbar) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (ENNReal.ofReal (C * a) ^ (2 * p)) ^ (1 / 2 : ℝ) *
        (ENNReal.ofReal (C * b) ^ (2 * p)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Cbar * C * a * b) ^ p := by
  have hsqrt (x : ℝ≥0∞) :
      (x ^ (2 * p)) ^ (1 / 2 : ℝ) = x ^ p := by
    rw [← ENNReal.rpow_natCast x (2 * p), ← ENNReal.rpow_mul]
    have he : ((2 * p : ℕ) : ℝ) * (1 / 2 : ℝ) = p := by
      push_cast
      ring
    rw [he, ENNReal.rpow_natCast]
  rw [hsqrt, hsqrt]
  rw [← mul_pow]
  rw [← ENNReal.ofReal_mul' (mul_nonneg hC hb)]
  have hCC : C * C ≤ Cbar * C :=
    mul_le_mul_of_nonneg_right hCbar hC
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have hprod : C * a * (C * b) ≤ Cbar * C * a * b := by
    calc
      C * a * (C * b) = (C * C) * (a * b) := by ring
      _ ≤ (Cbar * C) * (a * b) := mul_le_mul_of_nonneg_right hCC hab
      _ = Cbar * C * a * b := by ring
  exact ENNReal.pow_le_pow_left (ENNReal.ofReal_le_ofReal hprod)

end RegularityStructures

end
