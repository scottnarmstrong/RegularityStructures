/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovFieldNormMeasurable
public import RegularityStructures.Probability.ModelKolmogorovHSComponentNormMoment

/-!
# Assembly of the Pi and Gamma moments

This is the final algebraic assembly in the Kolmogorov criterion for models. The Pi and Gamma
estimates are supplied as actual component-norm moments; the predicates
`IsContinuousRandomModelWithFieldsOn` supply their measurability. No pathwise model-norm bound is
used here. The source-to-component estimates are proved separately for the Pi and Gamma halves.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace RegularityStructures

theorem randomModel_normOn_moment_le_of_component_moments
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (𝒯 : RegularityStructure ι)
    (Z₁ Z₂ : Ω → Model 𝒯 parabolicSemigroup)
    (S : Set ParabolicSpace) (γ : ℝ) (p : ℕ)
    (hp : 1 ≤ p)
    (hZ₁ : IsContinuousRandomModelWithFieldsOn Z₁ S)
    (hZ₂ : IsContinuousRandomModelWithFieldsOn Z₂ S)
    {A B AΔ BΔ : ℝ≥0∞}
    (hPi : ∀ Z ∈ ({Z₁, Z₂} : Set (Ω → Model 𝒯 parabolicSemigroup)),
      ∫⁻ ω, (Z ω).piNormOn γ S ^ p ∂P ≤ A)
    (hGamma : ∀ Z ∈ ({Z₁, Z₂} : Set (Ω → Model 𝒯 parabolicSemigroup)),
      ∫⁻ ω, (Z ω).gammaNormOn γ S ^ p ∂P ≤ B)
    (hPiΔ : ∫⁻ ω, (Z₁ ω).piDiffNormOn (Z₂ ω) γ S ^ p ∂P ≤ AΔ)
    (hGammaΔ : ∫⁻ ω, (Z₁ ω).gammaDiffNormOn (Z₂ ω) γ S ^ p ∂P ≤ BΔ) :
    (∀ Z ∈ ({Z₁, Z₂} : Set (Ω → Model 𝒯 parabolicSemigroup)),
      AEMeasurable (fun ω => (Z ω).normOn γ S) P ∧
        ∫⁻ ω, (Z ω).normOn γ S ^ p ∂P ≤
          (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) * (A + B)) ∧
    AEMeasurable (fun ω => (Z₁ ω).diffNormOn (Z₂ ω) γ S) P ∧
      ∫⁻ ω, (Z₁ ω).diffNormOn (Z₂ ω) γ S ^ p ∂P ≤
        (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) * (AΔ + BΔ) := by
  have hnorm₁ := randomModel_normOn_moment_le_of_component_norm_moments
    (M := Z₁) hp
      (hZ₁.measurable_piNormOn γ).aemeasurable
      (hZ₁.measurable_gammaNormOn γ).aemeasurable
      (hPi Z₁ (by simp)) (hGamma Z₁ (by simp))
  have hnorm₂ := randomModel_normOn_moment_le_of_component_norm_moments
    (M := Z₂) hp
      (hZ₂.measurable_piNormOn γ).aemeasurable
      (hZ₂.measurable_gammaNormOn γ).aemeasurable
      (hPi Z₂ (by simp)) (hGamma Z₂ (by simp))
  have hdiff := randomModel_diffNormOn_moment_le_of_component_norm_moments
    (M₁ := Z₁) (M₂ := Z₂) hp
      (hZ₁.measurable_piDiffNormOn hZ₂ γ).aemeasurable
      (hZ₁.measurable_gammaDiffNormOn hZ₂ γ).aemeasurable
      hPiΔ hGammaΔ
  refine ⟨?_, hdiff⟩
  intro Z hZ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hZ
  rcases hZ with rfl | rfl
  · exact hnorm₁
  · exact hnorm₂

end RegularityStructures

end
