module

public import GlobalPhi43.MW20.OnePointScalePowers

/-!
# Explicit one-point source coefficient on the scale range T≤L
-/

public section

namespace GlobalPhi43.MW20

/-- The first product after multiplication by T² and extraction of T^γ. -/
@[expose] noncomputable def sourceFirstProductScale (ε L M H Hv : ℝ) : ℝ :=
  L ^ (1 + 2 * ε) * M ^ (3 / 2 - ε) * H +
    L ^ (1 - 2 * ε) * M ^ (2 - 4 * ε) * Hv +
    L ^ (4 * ε) * M ^ (5 / 2 - ε) + L ^ (1 / 2 + ε) * M ^ (3 - 4 * ε) +
    L ^ (1 - 2 * ε) * M ^ (7 / 2 - 7 * ε)

/-- The second product with the same extracted regularity. -/
@[expose] noncomputable def sourceSecondProductScale (ε L M Hv HU Hν N : ℝ) : ℝ :=
  L ^ (1 - 2 * ε) *
      (Hv * M ^ (2 - 4 * ε) + (HU + Hν) * M ^ (1 - 2 * ε)) +
    M ^ (5 / 2 - 5 * ε) + L ^ (1 / 2 + ε) * M ^ (3 - 4 * ε) +
    L ^ (1 / 2 + 3 * ε) * N * M ^ (1 - 2 * ε)

/-- The explicit nonnegative one-point coefficient. All norms supplied here
are actual source quantities in the estimate theorem. -/
@[expose] noncomputable def sourceOnePointMajorant (ε L M H Hv HU Hν N c : ℝ) : ℝ :=
  L ^ (1 / 2 + 5 * ε) * M ^ 3 + c * Hv * M ^ (1 - 2 * ε) +
    c * sourceFirstProductScale ε L M H Hv + c * sourceSecondProductScale ε L M Hv HU Hν N

/-- The actual first-product scale extraction, with no extra smallness. -/
theorem sourceFirstProductBudget_heat_scale {ε T L M H Hv : ℝ}
    (hT : 0 < T) (hTL : T ≤ L) (hε : 0 ≤ ε) (hsmall : ε < 1 / 14)
    (hM : 0 ≤ M) (hH : 0 ≤ H) (hHv : 0 ≤ Hv) :
    T ^ 2 * sourceFirstProductBudget ε T M H Hv ≤
      sourceFirstProductScale ε L M H Hv * T ^ (3 / 2 - 5 * ε) := by
  obtain ⟨_, hα, hκ, hJ, hB, _, _⟩ := mw20_heat_test_powers hT hTL hε hsmall
  have h₁ := mul_le_mul_of_nonneg_right hα (show 0 ≤ M ^ (3 / 2 - ε) * H by positivity)
  have h₂ := mul_le_mul_of_nonneg_right hκ (show 0 ≤ M ^ (2 - 4 * ε) * Hv by positivity)
  have h₃ := mul_le_mul_of_nonneg_right hJ (Real.rpow_nonneg hM (5 / 2 - ε))
  have h₄ := mul_le_mul_of_nonneg_right hB (Real.rpow_nonneg hM (3 - 4 * ε))
  have h₅ := mul_le_mul_of_nonneg_right hκ (Real.rpow_nonneg hM (7 / 2 - 7 * ε))
  unfold sourceFirstProductBudget sourceFirstProductScale
  nlinarith only [h₁, h₂, h₃, h₄, h₅]

/-- The second-product extraction retains every renormalized budget additively. -/
theorem sourceSecondProductBudget_heat_scale {ε T L M Hv HU Hν N : ℝ}
    (hT : 0 < T) (hTL : T ≤ L) (hε : 0 ≤ ε) (hsmall : ε < 1 / 14)
    (hM : 0 ≤ M) (hHv : 0 ≤ Hv) (hHU : 0 ≤ HU) (hHν : 0 ≤ Hν) (hN : 0 ≤ N) :
    T ^ 2 * sourceSecondProductBudget ε T M Hv HU Hν N ≤
      sourceSecondProductScale ε L M Hv HU Hν N * T ^ (3 / 2 - 5 * ε) := by
  obtain ⟨_, _, hκ, _, hB, hD, hX⟩ := mw20_heat_test_powers hT hTL hε hsmall
  have h₁ := mul_le_mul_of_nonneg_right hκ
    (show 0 ≤ Hv * M ^ (2 - 4 * ε) + (HU + Hν) * M ^ (1 - 2 * ε) by positivity)
  have h₂ := mul_le_mul_of_nonneg_right hD (Real.rpow_nonneg hM (5 / 2 - 5 * ε))
  have h₃ := mul_le_mul_of_nonneg_right hB (Real.rpow_nonneg hM (3 - 4 * ε))
  have h₄ := mul_le_mul_of_nonneg_right hX (show 0 ≤ N * M ^ (1 - 2 * ε) by positivity)
  unfold sourceSecondProductBudget sourceSecondProductScale
  nlinarith only [h₁, h₂, h₃, h₄]

end GlobalPhi43.MW20
