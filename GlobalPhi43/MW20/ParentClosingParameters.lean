module

public import GlobalPhi43.Local.ScaleChoice

/-! Uniform k-then-c choice for the parent-amplitude (4.31) assembly. -/

public section

namespace GlobalPhi43.MW20

/-- Choose k before c, retaining any positive c cap imposed before.
The normalized row is an explicit arithmetic input, not a claim that the
analytic source row has already been assembled. -/
theorem exists_parent_closing_parameters {ε C cPrior : ℝ}
    (hsmall : ε < 1 / 14) (hC : 0 ≤ C) (hPrior : 0 < cPrior) :
    ∃ k : ℝ, 2 < k ∧ ∃ c₀ : ℝ, 0 < c₀ ∧ c₀ ≤ cPrior ∧ c₀ ≤ 1 ∧
      ∀ c : ℝ, 0 ≤ c → c ≤ c₀ → ∀ N M B : ℝ, 0 ≤ M →
      N ≤ C * max B (max (M * k ^ (-1 / 2 + 3 * ε))
        (max (M * k ^ (-1 / 6 + ε)) (M * (c * k ^ (3 / 2 + 3 * ε)) ^ (1 / 3 : ℝ)))) →
      N ≤ max (C * B) (M / 2) := by
  obtain ⟨k, hk, ha, hb⟩ := Local.exists_large_scale (C := C) hsmall
  obtain ⟨δ, hδ, hδ1, hp, _⟩ := Local.exists_small_constant C (k ^ (3 / 2 + 3 * ε))
  refine ⟨k, hk, min cPrior δ, lt_min hPrior hδ, min_le_left _ _,
    (min_le_right _ _).trans hδ1, ?_⟩
  intro c hc hcc N M B hM hrow
  have hcδ : c ≤ δ := hcc.trans (min_le_right _ _)
  have hk0 : 0 < k := by linarith
  have hrpow : (c * k ^ (3 / 2 + 3 * ε)) ^ (1 / 3 : ℝ) ≤
      (δ * k ^ (3 / 2 + 3 * ε)) ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow (by positivity)
      (mul_le_mul_of_nonneg_right hcδ (by positivity)) (by norm_num)
  have hcp : C * (c * k ^ (3 / 2 + 3 * ε)) ^ (1 / 3 : ℝ) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left hrpow hC).trans hp.le
  apply hrow.trans
  rw [mul_max_of_nonneg _ _ hC, mul_max_of_nonneg _ _ hC, mul_max_of_nonneg _ _ hC]
  apply max_le_max_left
  apply max_le
  · nlinarith [mul_le_mul_of_nonneg_left ha.le hM]
  · apply max_le
    · nlinarith [mul_le_mul_of_nonneg_left hb.le hM]
    · nlinarith [mul_le_mul_of_nonneg_left hcp hM]

end GlobalPhi43.MW20
