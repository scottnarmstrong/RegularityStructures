/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovContinuousRandomModel
public import RegularityStructures.Statements.Defs.IsContinuousRandomModelWithFieldsOn

/-!
# Measurability of the Gamma norms of continuous random models

This is the measurability part of the Kolmogorov criterion for models [Hai14, Theorem 10.7]. The
predicate `IsContinuousRandomModelWithFieldsOn` contains `IsContinuousRandomModelOn`, so the
Caratheodory argument for the actual compact Gamma supremum applies directly. No moment estimate or
model-norm bound is used here.
-/

@[expose] public section

open MeasureTheory

namespace RegularityStructures

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace Ω] {P : Measure Ω}
  {𝒯 : RegularityStructures.RegularityStructure ι}
  {Z : Ω → RegularityStructures.Model 𝒯
    RegularityStructures.parabolicSemigroup}
  {S : Set RegularityStructures.ParabolicSpace}

/-- The Gamma norm of a random model with continuous regularised fields is measurable. -/
theorem randomModel_gammaNormOn_aemeasurable_of_continuousWithFields
    (hZ : RegularityStructures.IsContinuousRandomModelWithFieldsOn Z S)
    (γ : ℝ) :
    AEMeasurable (fun ω => (Z ω).gammaNormOn γ S) P := by
  exact (RegularityStructures.IsContinuousRandomModelOn.measurable_gammaNormOn
    hZ.1 γ).aemeasurable

/-- The Gamma difference norm of two random models with continuous regularised fields is
measurable. -/
theorem randomModel_gammaDiffNormOn_aemeasurable_of_continuousWithFields
    {Z₁ Z₂ : Ω → RegularityStructures.Model 𝒯
      RegularityStructures.parabolicSemigroup}
    (hZ₁ : RegularityStructures.IsContinuousRandomModelWithFieldsOn Z₁ S)
    (hZ₂ : RegularityStructures.IsContinuousRandomModelWithFieldsOn Z₂ S)
    (γ : ℝ) :
    AEMeasurable
      (fun ω => (Z₁ ω).gammaDiffNormOn (Z₂ ω) γ S) P := by
  exact (RegularityStructures.IsContinuousRandomModelOn.measurable_gammaDiffNormOn
    hZ₁.1 hZ₂.1 γ).aemeasurable

end RegularityStructures

end
