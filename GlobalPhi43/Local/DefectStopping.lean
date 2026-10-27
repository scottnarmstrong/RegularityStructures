/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.DefectBudget

/-! The augmented-defect stopping alternative of the radius algorithm.
This is numerical arithmetic; actual sup norms and the halving theorem are not
supplied by this module. The common constant c is fixed before M and the data. -/
public section

namespace GlobalPhi43.Local

/-- Failure of either augmented defect test controls M by a constant times the
defect scale K, where E₁,E₃ have amplitude three and E₂ has amplitude two.
The factor 2/c depends only on the already chosen common smallness constant. -/
theorem mass_bound_of_defect_not_small {c M K E₁ E₂ E₃ : ℝ}
    (hc : 0 < c) (hc₁ : c ≤ 1) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hE₁ : E₁ ≤ K ^ 3) (hE₂ : E₂ ≤ K ^ 2) (hE₃ : E₃ ≤ K ^ 3)
    (hfail : ¬ DefectSmall c M E₁ E₂ E₃) :
    M ≤ (2 / c) * K := by
  by_contra hnot
  have hlarge : 2 * K < c * M := by
    have h := (div_lt_iff₀ hc).mp (show 2 * K / c < M by
      simpa [div_mul_eq_mul_div] using lt_of_not_ge hnot)
    nlinarith
  have hcM : c * M ≤ M := by nlinarith
  have hKM : K ≤ M := by linarith
  have hsq : K ^ 2 ≤ M ^ 2 := by nlinarith
  have hcub : 2 * K ^ 3 ≤ c * M ^ 3 := by
    have hp := mul_le_mul (show 2 * K ≤ c * M by linarith) hsq
      (sq_nonneg K) (mul_nonneg hc.le hM)
    nlinarith
  have hquad : K ^ 2 ≤ c * M ^ 2 := by
    have hp := mul_le_mul_of_nonneg_right (show 2 * K ≤ c * M by linarith) hM
    nlinarith [mul_le_mul_of_nonneg_left hKM hK]
  apply hfail
  unfold DefectSmall
  exact ⟨by linarith, hE₂.trans hquad⟩

end GlobalPhi43.Local
