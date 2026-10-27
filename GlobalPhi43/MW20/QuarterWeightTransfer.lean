module

public import GlobalPhi43.MW20.ParentScaleAlgebra

/-!
# Fixed quarter-inset weight transfer
-/

public section

namespace GlobalPhi43.MW20

/-- A quarter-scale weighted estimate transfers to the parent scale with a
uniform factor four for all scalar exponents between zero and one. -/
theorem quarter_weight_transfer {d a γ X A M C : ℝ}
    (hd : 0 < d) (ha1 : a ≤ 1) (hγ : 0 ≤ γ)
    (hX : 0 ≤ X) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hbound : (d / 4) ^ a * X ≤ C * ((d / 4) ^ γ * A + M)) :
    d ^ a * X ≤ 4 * C * (d ^ γ * A + M) := by
  have h4 : (4 : ℝ) ^ a ≤ 4 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) ha1
  have he : d ^ a = (4 : ℝ) ^ a * (d / 4) ^ a := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity : 0 ≤ d / 4)]
    congr 1
    ring
  have hg : (d / 4) ^ γ ≤ d ^ γ :=
    Real.rpow_le_rpow (by positivity) (by linarith) hγ
  calc
    _ = (4 : ℝ) ^ a * ((d / 4) ^ a * X) := by rw [he]; ring
    _ ≤ 4 * ((d / 4) ^ a * X) := mul_le_mul_of_nonneg_right h4 (by positivity)
    _ ≤ 4 * (C * ((d / 4) ^ γ * A + M)) := mul_le_mul_of_nonneg_left hbound (by norm_num)
    _ ≤ 4 * (C * (d ^ γ * A + M)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_right hg hA) (le_refl M)) hC)
        (by norm_num)
    _ = _ := by ring

/-- The exact transfer factor works also for the coefficient Holder weight
γ>1. No bound on X or on the exponent a is required. -/
theorem quarter_weight_transfer_exact {d a γ X A M C : ℝ}
    (hd : 0 < d) (hγ : 0 ≤ γ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hbound : (d / 4) ^ a * X ≤ C * ((d / 4) ^ γ * A + M)) :
    d ^ a * X ≤ (4 : ℝ) ^ a * C * (d ^ γ * A + M) := by
  have he : d ^ a = (4 : ℝ) ^ a * (d / 4) ^ a := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity : 0 ≤ d / 4)]
    congr 1
    ring
  have hg : (d / 4) ^ γ ≤ d ^ γ :=
    Real.rpow_le_rpow (by positivity) (by linarith) hγ
  calc
    _ = (4 : ℝ) ^ a * ((d / 4) ^ a * X) := by rw [he]; ring
    _ ≤ (4 : ℝ) ^ a * (C * ((d / 4) ^ γ * A + M)) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ ≤ (4 : ℝ) ^ a * (C * (d ^ γ * A + M)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_right hg hA) (le_refl M)) hC) (by positivity)
    _ = _ := by ring

end GlobalPhi43.MW20
