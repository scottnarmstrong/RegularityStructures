/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovHSDiagonal
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# Gamma norm moment conversion

This module converts pointwise random `GammaBoundOn` estimates into moments of the corresponding
best-constant `gammaNormOn`. The difference-model statement is the corresponding conversion for
`gammaDiffNormOn`. These are the Gamma-half inputs to the Kolmogorov criterion for models.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace RegularityStructures

theorem randomModel_gammaNormOn_moment_le_of_gammaBound
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P]
    {𝒯 : RegularityStructures.RegularityStructure ι}
    (M : Ω → RegularityStructures.Model 𝒯
      RegularityStructures.parabolicSemigroup)
    (γ : ℝ) (S : Set RegularityStructures.ParabolicSpace) (p : ℕ)
    {B : Ω → ℝ≥0∞} {A : ℝ≥0∞}
    (hB : ∀ᵐ ω ∂P, (M ω).GammaBoundOn γ (B ω).toNNReal S)
    (hBtop : ∀ᵐ ω ∂P, B ω ≠ ∞)
    (hMoment : ∫⁻ ω, B ω ^ p ∂P ≤ A) :
    ∫⁻ ω, (M ω).gammaNormOn γ S ^ p ∂P ≤ A := by
  refine (lintegral_mono_ae ?_).trans hMoment
  filter_upwards [hB, hBtop] with ω hBω hBtopω
  rw [← ENNReal.coe_toNNReal hBtopω]
  exact ENNReal.pow_le_pow_left
    ((Model.gammaNormOn_le_iff (M := M ω) (γ := γ) (S := S)
      (B ω).toNNReal).2 hBω)

theorem randomModel_gammaDiffNormOn_moment_le_of_gammaDiffBound
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P]
    {𝒯 : RegularityStructures.RegularityStructure ι}
    (M₁ M₂ : Ω → RegularityStructures.Model 𝒯
      RegularityStructures.parabolicSemigroup)
    (γ : ℝ) (S : Set RegularityStructures.ParabolicSpace) (p : ℕ)
    {B : Ω → ℝ≥0∞} {A : ℝ≥0∞}
    (hB : ∀ᵐ ω ∂P, (M₁ ω).GammaDiffBoundOn (M₂ ω) γ (B ω).toNNReal S)
    (hBtop : ∀ᵐ ω ∂P, B ω ≠ ∞)
    (hMoment : ∫⁻ ω, B ω ^ p ∂P ≤ A) :
    ∫⁻ ω, (M₁ ω).gammaDiffNormOn (M₂ ω) γ S ^ p ∂P ≤ A := by
  refine (lintegral_mono_ae ?_).trans hMoment
  filter_upwards [hB, hBtop] with ω hBω hBtopω
  rw [← ENNReal.coe_toNNReal hBtopω]
  exact ENNReal.pow_le_pow_left
    ((Model.gammaDiffNormOn_le_iff (M₁ ω) (M₂ ω) γ S
      (B ω).toNNReal).2 hBω)

end RegularityStructures

end
