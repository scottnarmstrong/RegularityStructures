module

public import GlobalPhi43.Attachment.ProbePieceNormalization
public import Mathlib.Analysis.SpecificLimits.Normed

/-! Summable numerical allowances after paying the three-dimensional cell count. -/

public noncomputable section

namespace GlobalPhi43.Attachment

theorem probePieceFactor_inv_fifth (n : ℕ) :
    ((probePieceFactor n)⁻¹)^5 = (1/32 : ℝ)*(1/32 : ℝ)^n := by
  unfold probePieceFactor
  rw [inv_pow, ← pow_mul, Nat.mul_comm (n+1) 5, pow_mul, pow_succ]
  norm_num [one_div]
  simp only [one_div, inv_pow]

theorem probe_folded_geometric_cost (n : ℕ) :
    (2 : ℝ)^(3*n)*((probePieceFactor n)⁻¹)^5 = (1/32 : ℝ)*(1/4 : ℝ)^n := by
  rw [probePieceFactor_inv_fifth, mul_left_comm, pow_mul, ← mul_pow]
  norm_num

theorem probe_small_geometric_cost (n : ℕ) :
    ((probePieceFactor n)⁻¹)^5 ≤ (1/4 : ℝ)^n := by
  rw [probePieceFactor_inv_fifth]
  calc (1/32 : ℝ)*(1/32 : ℝ)^n ≤ 1*(1/32 : ℝ)^n :=
      mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ ≤ (1/4 : ℝ)^n := by
      rw [one_mul]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) n
end GlobalPhi43.Attachment
