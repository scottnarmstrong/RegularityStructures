/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.GenericScaleRecurrence
public import GlobalPhi43.Local.ActualScaleRecurrence

/-! The generic actual recurrence uses the one-point forcing bound only at L<=d/8.
This avoids pricing unused larger one-point radii in the native application. -/
@[expose] public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 MeasureTheory Set
open scoped ContDiff ENNReal

 theorem exists_generic_scale_recurrence_small_P2 {I J : Type*}
    (A : Finset I) (α : I → ℝ) (B : Finset J) (β : J → ℝ)
    {γ : ℝ} (hγ : 1 < γ) (hγ₂ : γ ≤ 2)
    (hβ : ∀ j ∈ B, 0 ≤ β j) (hβγ : ∀ j ∈ B, β j ≤ γ) :
    ∃ C > 0, ∀ (ε : ℝ), 0 < ε → ε ≤ 1 / 4 →
      ∀ (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) (U : GermPoint → ℝ)
        (r d₀ M₁ M₂ : ℝ), 0 ≤ r → 0 ≤ M₁ → 0 ≤ M₂ →
      (∃ O : Set GermPoint, IsOpen O ∧
        closure (sourceCylinder r) ×ˢ closure (sourceCylinder r) ⊆ O ∧ ContDiffOn ℝ ∞ U O) →
      (∀ x ∈ sourceCylinder r, U (x, x) = 0) →
      (∀ d ∈ Ioc (0 : ℝ) d₀, ∀ x ∈ cylinderInterior r d,
        ∀ b ∈ sourceCylinder r, b ∈ symmetricBall x (d / 2) →
        ∀ z ∈ sourceCylinder r, z ∈ symmetricBall b (d / 4) →
        d ^ γ * |U (x, z) - U (x, b) - U (b, z)| ≤
          M₂ * ∑ j ∈ B, pdist x b ^ β j * pdist b z ^ (γ - β j)) →
      (∀ d ∈ Ioc (0 : ℝ) d₀, ∀ x ∈ cylinderInterior r d,
        ∀ (L : ℝ), 0 < L → L ≤ d / 8 → ∀ (T : ℝ) (hT : 0 < T), T ≤ L →
        d ^ γ * T ^ 2 * (localScalarSup (fun y => ∫ w,
          sourceHeat (fun z => U (x, z)) (y + w) ∂infiniteKernelMeasure Φ hΦ T hT)
            (pastBall x L)).toReal ≤ M₁ * ∑ i ∈ A, T ^ α i * L ^ (γ - α i)) →
      let F := (weightedPastAffineError U r d₀ (1 / 8) γ).toReal
      let Q := (smallPastRemainderSeminorm U (diagonalSpatialCoefficient U) r d₀ (ε / 32) γ).toReal
      F ≤ (C * ε ^ (2 - γ)) * F +
        (genericCaloricDataBudget A α B β γ C ε M₁ M₂ +
          (8 / ε) ^ γ * (radiusSourceUSup U r d₀).toReal) +
        ((8 / 7 : ℝ) ^ γ * (ε ^ γ + C * ε ^ (2 + γ))) * Q := by
  obtain ⟨C, hC, hstep⟩ := exists_generic_normalized_caloric_step A α B β hγ hγ₂ hβ hβγ
  refine ⟨C, hC, ?_⟩
  intro ε hε hεsmall Φ hΦ U r d₀ M₁ M₂ hr hM₁ hM₂ hU hdiag hthree hP2
  have hBfinite := radiusSourceUSup_ne_top U (d₀ := d₀) hr hU
  have hFfinite := weightedPastAffineError_ne_top U (d₀ := d₀) hr
    (by norm_num : (1 / 8 : ℝ) ≤ 1) (by linarith) hγ₂ hU
  apply actual_scale_recurrence U hBfinite (by norm_num : (1 / 8 : ℝ) ≤ 1 / 2)
    hε (by linarith) (by positivity) (by positivity)
    (by unfold genericCaloricDataBudget; positivity)
  intro d hd x hx R hR hRsmall
  let L := R / ε
  have hL : 0 < L := div_pos hR.1 hε
  have hLd : L ≤ d / 8 := (div_le_iff₀ hε).mpr (by nlinarith)
  have hR_eq : ε * L = R := by dsimp [L]; field_simp
  have hlarge : ENNReal.ofReal (d ^ γ * L ^ (-γ)) * pastAffineError (fun y => U (x, y)) x L ≤
      ENNReal.ofReal (weightedPastAffineError U r d₀ (1 / 8) γ).toReal := by
    have hLe : L ≤ (1 / 8 : ℝ) * d := by linarith
    have hs : ENNReal.ofReal (d ^ γ / L ^ γ) * pastAffineError (fun y => U (x, y)) x L ≤
        weightedPastAffineError U r d₀ (1 / 8) γ :=
      le_iSup_of_le d (le_iSup_of_le hd (le_iSup_of_le x (le_iSup_of_le hx
        (le_iSup_of_le L (le_iSup_of_le ⟨hL, hLe⟩ le_rfl)))))
    simpa only [Real.rpow_neg hL.le, div_eq_mul_inv] using
      hs.trans_eq (ENNReal.ofReal_toReal hFfinite).symm
  have hh := hstep Φ hΦ U r d₀ d ε L M₁ M₂ _ hε hL hr hd hεsmall hLd hM₁ hM₂
    ENNReal.toReal_nonneg hU hdiag x hx (hthree d hd x hx) hlarge
    (hP2 d hd x hx L hL hLd (ε ^ 2 * L) _
      (mul_le_of_le_one_left hL.le (by nlinarith : ε ^ 2 ≤ 1)))
  rw [hR_eq] at hh
  simpa only [genericCaloricDataBudget, Real.rpow_neg hR.1.le, div_eq_mul_inv,
    add_assoc, mul_assoc] using hh

end GlobalPhi43.Local
