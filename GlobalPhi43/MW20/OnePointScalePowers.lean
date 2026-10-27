module

public import GlobalPhi43.MW20.SmallScaleForcingBudget

/-!
# Exact one-point scale powers from the heat forcing
-/

public section

namespace GlobalPhi43.MW20

/-- Extract any target regularity from a tested heat term with no loss of
power. The only scale comparison is the source T≤L. -/
theorem heat_test_power {T L q γ : ℝ} (hT : 0 < T) (hTL : T ≤ L) (hq : γ ≤ 2 + q) :
    T ^ (2 : ℕ) * T ^ q ≤ L ^ (2 + q - γ) * T ^ γ := by
  calc
    _ = T ^ ((2 : ℝ) + q) := by rw [← Real.rpow_two, ← Real.rpow_add hT]
    _ = T ^ (2 + q - γ) * T ^ γ := by rw [← Real.rpow_add hT]; congr 1; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hT.le hTL (by linarith)) (Real.rpow_nonneg hT.le γ)

/-- The source exponents after heat weighting, recorded with their exact L powers. -/
theorem mw20_heat_test_powers {T L ε : ℝ} (hT : 0 < T) (hTL : T ≤ L)
    (hε : 0 ≤ ε) (hsmall : ε < 1 / 14) :
    T ^ 2 ≤ L ^ (1 / 2 + 5 * ε) * T ^ (3 / 2 - 5 * ε) ∧
    T ^ 2 * T ^ (1 / 2 - 3 * ε) ≤ L ^ (1 + 2 * ε) * T ^ (3 / 2 - 5 * ε) ∧
    T ^ 2 * T ^ (1 / 2 - 7 * ε) ≤ L ^ (1 - 2 * ε) * T ^ (3 / 2 - 5 * ε) ∧
    T ^ 2 * T ^ (-(1 / 2) - ε) ≤ L ^ (4 * ε) * T ^ (3 / 2 - 5 * ε) ∧
    T ^ 2 * T ^ (-4 * ε) ≤ L ^ (1 / 2 + ε) * T ^ (3 / 2 - 5 * ε) ∧
    T ^ 2 * T ^ (-(1 / 2) - 5 * ε) ≤ T ^ (3 / 2 - 5 * ε) ∧
    T ^ 2 * T ^ (-2 * ε) ≤ L ^ (1 / 2 + 3 * ε) * T ^ (3 / 2 - 5 * ε) := by
  have he (q : ℝ) : (2 + q) - (3 / 2 - 5 * ε) = 1 / 2 + q + 5 * ε := by ring
  have h₀ := heat_test_power (q := 0) (γ := 3 / 2 - 5 * ε) hT hTL (by linarith)
  have h₁ := heat_test_power (q := 1 / 2 - 3 * ε) (γ := 3 / 2 - 5 * ε) hT hTL (by linarith)
  have h₂ := heat_test_power (q := 1 / 2 - 7 * ε) (γ := 3 / 2 - 5 * ε) hT hTL (by linarith)
  have h₃ := heat_test_power (q := -(1 / 2) - ε) (γ := 3 / 2 - 5 * ε) hT hTL (by linarith)
  have h₄ := heat_test_power (q := -4 * ε) (γ := 3 / 2 - 5 * ε) hT hTL (by linarith)
  have h₅ := heat_test_power (q := -(1 / 2) - 5 * ε) (γ := 3 / 2 - 5 * ε) hT hTL (by linarith)
  have h₆ := heat_test_power (q := -2 * ε) (γ := 3 / 2 - 5 * ε) hT hTL (by linarith)
  have e₀ : (2 : ℝ) + 0 - (3 / 2 - 5 * ε) = 1 / 2 + 5 * ε := by ring
  have e₁ : (2 : ℝ) + (1 / 2 - 3 * ε) - (3 / 2 - 5 * ε) = 1 + 2 * ε := by ring
  have e₂ : (2 : ℝ) + (1 / 2 - 7 * ε) - (3 / 2 - 5 * ε) = 1 - 2 * ε := by ring
  have e₃ : (2 : ℝ) + (-(1 / 2) - ε) - (3 / 2 - 5 * ε) = 4 * ε := by ring
  have e₄ : (2 : ℝ) + -4 * ε - (3 / 2 - 5 * ε) = 1 / 2 + ε := by ring
  have e₅ : (2 : ℝ) + (-(1 / 2) - 5 * ε) - (3 / 2 - 5 * ε) = 0 := by ring
  have e₆ : (2 : ℝ) + -2 * ε - (3 / 2 - 5 * ε) = 1 / 2 + 3 * ε := by ring
  exact ⟨by simpa only [e₀, Real.rpow_zero, mul_one] using h₀,
    by simpa only [e₁] using h₁, by simpa only [e₂] using h₂,
    by simpa only [e₃] using h₃, by simpa only [e₄] using h₄,
    by simpa only [e₅, Real.rpow_zero, one_mul] using h₅, by simpa only [e₆] using h₆⟩

end GlobalPhi43.MW20
