/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.AugmentedSchauderApplication
public import GlobalPhi43.Local.AugmentedAbsorptionCap

/-! Localized source estimates, bounded defects and the generic radius
estimate give an absorbed bound. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 MeasureTheory Set
open scoped ContDiff ENNReal

 theorem exists_absorbed_augmented_schauder_application {I J : Type*}
    (A : Finset I) (α : I → ℝ) (B : Finset J) (β : J → ℝ) (hA : A.Nonempty)
    {γ : ℝ} (hγ : 1 < γ) (hγ₂ : γ < 2)
    (hαγ : ∀ i ∈ A, α i ≤ γ) (hβ : ∀ j ∈ B, 0 ≤ β j) (hβγ : ∀ j ∈ B, β j ≤ γ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ c₀ > 0, c₀ ≤ 1 ∧ ∃ Aout > 0, ∀ (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) (U : GermPoint → ℝ)
      (G : (T : ℝ) → 0 < T → ParabolicSpace → ParabolicSpace → ℝ)
      (r M c M₁ M₂ E₁ E₂ E₃ : ℝ), 0 ≤ r → 0 < M → 0 ≤ c → c ≤ c₀ →
      0 ≤ M₁ → 0 ≤ M₂ → 0 ≤ E₁ → 0 ≤ E₂ → 0 ≤ E₃ → DefectSmall c M E₁ E₂ E₃ →
      (∃ O : Set GermPoint, IsOpen O ∧
        closure (sourceCylinder r) ×ˢ closure (sourceCylinder r) ⊆ O ∧ ContDiffOn ℝ ∞ U O) →
      (∀ x ∈ sourceCylinder r, U (x, x) = 0) →
      (∀ d ∈ Ioc (0 : ℝ) (M⁻¹), ∀ x ∈ cylinderInterior r d,
        ∀ b ∈ sourceCylinder r, b ∈ symmetricBall x (d / 2) →
        ∀ z ∈ sourceCylinder r, z ∈ symmetricBall b (d / 4) →
        d ^ γ * |U (x, z) - U (x, b) - U (b, z)| ≤
          M₂ * ∑ j ∈ B, pdist x b ^ β j * pdist b z ^ (γ - β j)) →
      (∀ d ∈ Ioc (0 : ℝ) (M⁻¹), ∀ x ∈ cylinderInterior r d,
        ∀ (L : ℝ), 0 < L → L ≤ d / 8 → ∀ (T : ℝ) (hT : 0 < T), T ≤ L →
        ∀ y ∈ pastBall x L,
        |sourceHeat (pastSmooth (infiniteKernelMeasure Φ hΦ T hT) (fun z => U (x, z))) y -
          G T hT x y| ≤ E₁ + E₃ + 3 * M * E₂) →
      (∀ d ∈ Ioc (0 : ℝ) (M⁻¹), ∀ x ∈ cylinderInterior r d,
        ∀ (L : ℝ), 0 < L → L ≤ d / 8 → ∀ (T : ℝ) (hT : 0 < T), T ≤ L →
        ∀ y ∈ pastBall x L, d ^ γ * T ^ 2 * |G T hT x y| ≤
          M₁ * ∑ i ∈ A, T ^ α i * L ^ (γ - α i)) →
      ((radiusSourceUSup U r (M⁻¹)).toReal + M₁ + M₂ ≤
        C * (M + c * ((weightedRadiusAffineSeminorm U r (M⁻¹) γ).toReal + M))) →
      weightedRadiusAffineSeminorm U r (M⁻¹) γ ≤ ENNReal.ofReal (Aout * M) := by
  obtain ⟨K, hK, happly⟩ := exists_augmented_schauder_application A α B β hA hγ hγ₂ hαγ hβ hβγ
  obtain ⟨c₀, hc₀, hc₀1, Aout, hAout, habs⟩ := exists_augmented_absorption_cap hK hC
  refine ⟨c₀, hc₀, hc₀1, Aout, hAout, ?_⟩
  intro Φ hΦ U G r M c M₁ M₂ E₁ E₂ E₃ hr hM hc hcc hM₁ hM₂ hE₁ hE₂ hE₃ hsmall
    hU hdiag hthree herror hbase hprice
  let F := E₁ + E₃ + 3 * M * E₂
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hnorm := happly Φ hΦ U G r (M⁻¹) M₁ M₂ F hr hM₁ hM₂ hF
    hU hdiag hthree herror hbase
  have hfinite := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hnorm
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hnorm
  rw [ENNReal.toReal_ofReal (by positivity)] at hreal
  have hdef : (M⁻¹) ^ 2 * F ≤ 4 * c * M := by
    simpa only [F, one_mul, mul_one] using!
      defect_insertion_at_natural_radius (C := 1) (by norm_num) hM hsmall
  have hsum := add_le_add hprice hdef
  have hbound := hreal.trans (mul_le_mul_of_nonneg_left hsum hK.le)
  have hout := habs M (weightedRadiusAffineSeminorm U r (M⁻¹) γ).toReal c hM.le
    ENNReal.toReal_nonneg hc hcc hbound
  calc
    _ = ENNReal.ofReal (weightedRadiusAffineSeminorm U r (M⁻¹) γ).toReal :=
      (ENNReal.ofReal_toReal hfinite).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hout

end GlobalPhi43.Local
