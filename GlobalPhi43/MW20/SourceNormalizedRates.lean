module

public import GlobalPhi43.Local.CausalAbsorption
public import GlobalPhi43.MW20.SourceSchauderExponents

/-! Fixed coefficients of the normalized source recurrence. -/

public section

namespace GlobalPhi43.MW20

/-- The coefficient of the actual affine-error supremum. -/
@[expose] noncomputable def sourceNormalizedHeatRate (C η γ : ℝ) : ℝ := C * η ^ (2 - γ)

/-- The coefficient of the actual sampled causal remainder, with exact depth loss. -/
@[expose] noncomputable def sourceNormalizedRemainderRate (C η γ : ℝ) : ℝ :=
  (8 / 7 : ℝ) ^ γ * (η ^ γ + C * η ^ (2 + γ))


/-- Both absorption choices precede the source fields and all norms. The
coefficient H is the fixed Campanato comparison factor, not a datum. -/
theorem exists_source_normalized_absorption_scale {γ C H : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hC : 0 ≤ C) (hH : 0 ≤ H) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 4 ∧
      sourceNormalizedHeatRate C η γ ≤ 1 / 2 ∧
      sourceNormalizedRemainderRate C η γ * H ≤ 1 / 4 := by
  obtain ⟨η, hη, hq, hheat, hrem⟩ :=
    Local.exists_causal_absorption_parameter hγ hγ2 C (2 * (C + 1) * H)
  have h₁ := Real.rpow_nonneg hη.le γ
  have h₂ := Real.rpow_nonneg hη.le (2 + γ)
  have h₇ : 0 ≤ (8 / 7 : ℝ) ^ γ := by positivity
  have hb : η ^ γ + C * η ^ (2 + γ) ≤ (C + 1) * (η ^ γ + η ^ (2 + γ)) := by
    nlinarith only [mul_nonneg hC h₁, h₂]
  have hw := mul_le_mul_of_nonneg_right hb (mul_nonneg hH h₇)
  refine ⟨η, hη, hq.le, hheat.le, ?_⟩
  unfold sourceNormalizedRemainderRate
  nlinarith only [hw, hrem]

end GlobalPhi43.MW20
