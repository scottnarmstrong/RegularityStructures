module

public import GlobalPhi43.Local.ScaleNormalization
public import Mathlib.Algebra.BigOperators.Field

/-! Exact normalization of the source smoothing errors and 7/8 depth loss. -/

public section

namespace GlobalPhi43.MW20

open scoped BigOperators

/-- The fixed depth loss has no dependence on the source scale. -/
theorem radius_smoothing_depth_factor {d γ : ℝ} (hd : 0 < d) :
    d ^ γ / (7 * d / 8) ^ γ = (8 / 7 : ℝ) ^ γ := by
  have he : d / (7 * d / 8) = (8 / 7 : ℝ) := by field_simp
  rw [← Real.div_rpow hd.le (by positivity : 0 ≤ 7 * d / 8), he]

/-- Normalize the two actual smoothing allowances before specializing the
near or far comparison weight. No error estimate is supplied implicitly. -/
theorem radius_smoothing_weight {d γ W E M Q A B : ℝ} (hd : 0 < d) (hW : 0 ≤ W)
    (he : E ≤ (M / d ^ γ) * A + (Q / (7 * d / 8) ^ γ) * B) :
    d ^ γ * W * E ≤ M * (W * A) + (8 / 7 : ℝ) ^ γ * Q * (W * B) := by
  have hp : d ^ γ ≠ 0 := (Real.rpow_pos_of_pos hd γ).ne'
  have hq : (7 * d / 8) ^ γ ≠ 0 := (Real.rpow_pos_of_pos (by positivity) γ).ne'
  calc
    _ ≤ d ^ γ * W * ((M / d ^ γ) * A + (Q / (7 * d / 8) ^ γ) * B) :=
      mul_le_mul_of_nonneg_left he (mul_nonneg (Real.rpow_nonneg hd.le γ) hW)
    _ = M * (W * A) + (d ^ γ / (7 * d / 8) ^ γ) * Q * (W * B) := by field_simp
    _ = _ := by rw [radius_smoothing_depth_factor hd]

/-- The normalized near smoothing term has exactly eta^(gamma-a) and
eta^gamma, including the fixed (8/7)^gamma remainder allowance. -/
theorem radius_smoothing_normalization_near {I : Type*} (A : Finset I) (β : I → ℝ)
    {d γ η L E M Q : ℝ} (hd : 0 < d) (hη : 0 < η) (hL : 0 < L)
    (he : E ≤ (M / d ^ γ) * (∑ i ∈ A, (η * L) ^ (β i) * (η ^ 2 * L) ^ (γ - β i)) +
      (Q / (7 * d / 8) ^ γ) * (η ^ 2 * L) ^ γ) :
    d ^ γ * (η * L) ^ (-γ) * E ≤
      M * (∑ i ∈ A, η ^ (γ - β i)) + (8 / 7 : ℝ) ^ γ * Q * η ^ γ := by
  have hh := radius_smoothing_weight hd (Real.rpow_nonneg (mul_pos hη hL).le (-γ)) he
  have ha : (η * L) ^ (-γ) * (∑ i ∈ A, (η * L) ^ (β i) * (η ^ 2 * L) ^ (γ - β i)) =
      ∑ i ∈ A, η ^ (γ - β i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [mul_assoc] using GlobalPhi43.Local.normalized_near_smoothing_power (β := β i) hη hL
  have hb := GlobalPhi43.Local.normalized_near_smoothing_power (γ := γ) (β := 0) hη hL
  simp only [Real.rpow_zero, mul_one, sub_zero] at hb
  rwa [ha, hb] at hh

/-- The normalized far term retains the exact exponent 2+gamma-2a. -/
theorem radius_smoothing_normalization_far {I : Type*} (A : Finset I) (β : I → ℝ)
    {d γ η L E M Q : ℝ} (hd : 0 < d) (hη : 0 < η) (hL : 0 < L)
    (he : E ≤ (M / d ^ γ) * (∑ i ∈ A, L ^ (β i) * (η ^ 2 * L) ^ (γ - β i)) +
      (Q / (7 * d / 8) ^ γ) * (η ^ 2 * L) ^ γ) :
    d ^ γ * ((η * L) ^ (-γ) * ((η * L) / L) ^ 2) * E ≤
      M * (∑ i ∈ A, η ^ (2 + γ - 2 * β i)) + (8 / 7 : ℝ) ^ γ * Q * η ^ (2 + γ) := by
  have hh := radius_smoothing_weight hd
    (mul_nonneg (Real.rpow_nonneg (mul_pos hη hL).le (-γ)) (sq_nonneg ((η * L) / L))) he
  have ha : ((η * L) ^ (-γ) * ((η * L) / L) ^ 2) *
      (∑ i ∈ A, L ^ (β i) * (η ^ 2 * L) ^ (γ - β i)) =
      ∑ i ∈ A, η ^ (2 + γ - 2 * β i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [mul_assoc] using GlobalPhi43.Local.normalized_far_smoothing_power (β := β i) hη hL
  have hb := GlobalPhi43.Local.normalized_far_smoothing_power (γ := γ) (β := 0) hη hL
  simp only [Real.rpow_zero, mul_one, mul_zero, sub_zero] at hb
  rwa [ha, hb] at hh

end GlobalPhi43.MW20
