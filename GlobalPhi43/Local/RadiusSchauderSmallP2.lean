/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.GenericSmallP2Recurrence
public import GlobalPhi43.Local.ActualNormAbsorption
public import GlobalPhi43.MW20.SourceNormalizedRates

/-! The generic radius estimate needs the one-point forcing bound only on L<=d/8.
The auxiliary scale and every constant are chosen before all source data. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 MeasureTheory Set
open scoped ContDiff ENNReal

 theorem exists_radius_schauder_small_P2 {I J : Type*}
    (A : Finset I) (α : I → ℝ) (B : Finset J) (β : J → ℝ)
    {γ : ℝ} (hγ : 1 < γ) (hγ₂ : γ < 2)
    (hβ : ∀ j ∈ B, 0 ≤ β j) (hβγ : ∀ j ∈ B, β j ≤ γ) :
    ∃ K > 0, ∀ (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) (U : GermPoint → ℝ)
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
      weightedRadiusAffineSeminorm U r d₀ γ ≤
        ENNReal.ofReal (K * ((radiusSourceUSup U r d₀).toReal + M₁ + M₂)) := by
  obtain ⟨C, hC, hrec⟩ := exists_generic_scale_recurrence_small_P2 A α B β hγ hγ₂.le hβ hβγ
  obtain ⟨ε, hε, hεq, hheat, hrem⟩ := exists_source_normalized_absorption_scale
    (by linarith : 0 < γ) hγ₂ hC.le (campanatoFactor_pos hγ).le
  have ha : C * ε ^ (2 - γ) ≤ 1 / 2 := hheat
  have hb : ((8 / 7 : ℝ) ^ γ * (ε ^ γ + C * ε ^ (2 + γ))) * campanatoFactor γ ≤ 1 / 4 := hrem
  obtain ⟨K, hK, hbound⟩ := actual_norm_absorption B β
    (θ := 1 / 8) (η := ε / 32) (a := C * ε ^ (2 - γ))
    (b := (8 / 7 : ℝ) ^ γ * (ε ^ γ + C * ε ^ (2 + γ)))
    (by positivity) (by linarith) (by norm_num) (by linarith)
    hγ hγ₂.le hβγ ha hb
  let W₁ := C * ∑ i ∈ A, ε ^ (2 * α i - 4 - γ)
  let W₂ := (∑ j ∈ B, ε ^ (γ - β j)) + C * (∑ j ∈ B, ε ^ (2 + γ - 2 * β j))
  let H := (8 / ε) ^ γ
  have hW₁ : 0 ≤ W₁ := by dsimp [W₁]; positivity
  have hW₂ : 0 ≤ W₂ := by dsimp [W₂]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  refine ⟨K * (1 + H + W₁ + W₂), by positivity, ?_⟩
  intro Φ hΦ U r d₀ M₁ M₂ hr hM₁ hM₂ hU hdiag hthree hP2
  let B₀ := (radiusSourceUSup U r d₀).toReal
  let P := genericCaloricDataBudget A α B β γ C ε M₁ M₂ + H * B₀
  have hP : 0 ≤ P := by dsimp [P, genericCaloricDataBudget, H, B₀]; positivity
  have hscale := hrec ε hε hεq Φ hΦ U r d₀ M₁ M₂ hr hM₁ hM₂ hU hdiag hthree hP2
  have hout := hbound U r d₀ P M₂ hr hP hM₂ hU hdiag hscale hthree
  apply hout.trans
  apply ENNReal.ofReal_le_ofReal
  have hB₀ : 0 ≤ B₀ := ENNReal.toReal_nonneg
  have hbudget : B₀ + P + M₂ ≤ (1 + H + W₁ + W₂) * (B₀ + M₁ + M₂) := by
    dsimp [P, genericCaloricDataBudget, W₁, W₂] at *
    nlinarith [mul_nonneg hW₁ hB₀, mul_nonneg hW₁ hM₂, mul_nonneg hW₂ hB₀,
      mul_nonneg hW₂ hM₁, mul_nonneg hH hM₁, mul_nonneg hH hM₂]
  have hh := mul_le_mul_of_nonneg_left hbudget hK.le
  simpa only [B₀, mul_assoc] using hh

end GlobalPhi43.Local
