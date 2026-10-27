module

public import GlobalPhi43.MW20.FirstProductBudget
public import GlobalPhi43.MW20.SecondProductBudget

/-!
# The complete parent forcing budget in MW20 (4.4)
-/

public section

namespace GlobalPhi43.MW20

/-- The five parent-amplitude terms on the right of (4.2), before c. -/
@[expose] noncomputable def sourceFirstProductBudget (ε T M H Hv : ℝ) : ℝ :=
  T ^ (1 / 2 - 3 * ε) * M ^ (3 / 2 - ε) * H +
    T ^ (1 / 2 - 7 * ε) * M ^ (2 - 4 * ε) * Hv +
    T ^ (-(1 / 2) - ε) * M ^ (5 / 2 - ε) + T ^ (-4 * ε) * M ^ (3 - 4 * ε) +
    T ^ (1 / 2 - 7 * ε) * M ^ (7 / 2 - 7 * ε)

/-- The complete renormalized second-product budget (4.3), before c. -/
@[expose] noncomputable def sourceSecondProductBudget (ε T M Hv HU Hν N : ℝ) : ℝ :=
  T ^ (1 / 2 - 7 * ε) *
      (Hv * M ^ (2 - 4 * ε) + (HU + Hν) * M ^ (1 - 2 * ε)) +
    M ^ (5 / 2 - 5 * ε) * T ^ (-(1 / 2) - 5 * ε) +
    T ^ (-4 * ε) * M ^ (3 - 4 * ε) + N * M ^ (1 - 2 * ε) * T ^ (-2 * ε)

/-- The comparison constant is fixed before all data, c, k and counterterms. -/
@[expose] noncomputable def smallScaleForcingConstant (ε : ℝ) : ℝ :=
  3 + 6 * firstProductConstant ε + 3 * secondProductConstant ε

/-- Scalar assembly of the four already proved actual forcing components. -/
theorem small_scale_forcing_assemble {ε q m e p₁ p₂ f₁ f₂ c : ℝ}
    (hsmall : ε < 1 / 14) (hm : 0 ≤ m) (he : 0 ≤ e)
    (hf₁ : 0 ≤ f₁) (hf₂ : 0 ≤ f₂) (hc : 0 ≤ c)
    (hq : q ≤ m + 3 * p₁ + 3 * e + 3 * p₂)
    (hp₁ : p₁ ≤ (2 * firstProductConstant ε) * c * f₁)
    (hp₂ : p₂ ≤ secondProductConstant ε * c * f₂) :
    q ≤ smallScaleForcingConstant ε * (m + e + c * f₁ + c * f₂) := by
  have hK₁ := (firstProductConstant_pos hsmall).le
  have hK₂ := (secondProductConstant_pos hsmall).le
  have hC₁ : 1 ≤ smallScaleForcingConstant ε := by unfold smallScaleForcingConstant; linarith
  have hC₃ : 3 ≤ smallScaleForcingConstant ε := by unfold smallScaleForcingConstant; linarith
  have hCP₁ : 6 * firstProductConstant ε ≤ smallScaleForcingConstant ε := by
    unfold smallScaleForcingConstant; linarith
  have hCP₂ : 3 * secondProductConstant ε ≤ smallScaleForcingConstant ε := by
    unfold smallScaleForcingConstant; linarith
  have h₁ := mul_le_mul_of_nonneg_right hC₁ hm
  have h₂ := mul_le_mul_of_nonneg_right hC₃ he
  have h₃ := mul_le_mul_of_nonneg_right hCP₁ (mul_nonneg hc hf₁)
  have h₄ := mul_le_mul_of_nonneg_right hCP₂ (mul_nonneg hc hf₂)
  nlinarith only [hq, hp₁, hp₂, h₁, h₂, h₃, h₄]

end GlobalPhi43.MW20
