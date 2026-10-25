/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovContinuousRandomModel
public import RegularityStructures.Statements.Defs.IsContinuousRandomModelWithFieldsOn

/-!
# Measurable model norms for random models with continuous regularised fields

The predicate `IsContinuousRandomModelWithFieldsOn` strengthens `IsContinuousRandomModelOn` by
adding whole-space regularised-field continuity. Its first conjunct is therefore already sufficient
for the compact model-norm measurability results, which are restated here for the stronger
predicate.
-/

public section

open MeasureTheory

namespace RegularityStructures

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace Ω]
  {𝒯 : RegularityStructures.RegularityStructure ι}
  {Z Z₁ Z₂ : Ω → RegularityStructures.Model 𝒯
    RegularityStructures.parabolicSemigroup}
  {S : Set RegularityStructures.ParabolicSpace}

theorem IsContinuousRandomModelWithFieldsOn.measurable_piNormOn
    (hZ : RegularityStructures.IsContinuousRandomModelWithFieldsOn Z S) (γ : ℝ) :
    Measurable (fun ω => (Z ω).piNormOn γ S) :=
  hZ.1.measurable_piNormOn γ

theorem IsContinuousRandomModelWithFieldsOn.measurable_gammaNormOn
    (hZ : RegularityStructures.IsContinuousRandomModelWithFieldsOn Z S) (γ : ℝ) :
    Measurable (fun ω => (Z ω).gammaNormOn γ S) :=
  hZ.1.measurable_gammaNormOn γ

theorem IsContinuousRandomModelWithFieldsOn.measurable_piDiffNormOn
    (hZ₁ : RegularityStructures.IsContinuousRandomModelWithFieldsOn Z₁ S)
    (hZ₂ : RegularityStructures.IsContinuousRandomModelWithFieldsOn Z₂ S) (γ : ℝ) :
    Measurable (fun ω => (Z₁ ω).piDiffNormOn (Z₂ ω) γ S) :=
  hZ₁.1.measurable_piDiffNormOn hZ₂.1 γ

theorem IsContinuousRandomModelWithFieldsOn.measurable_gammaDiffNormOn
    (hZ₁ : RegularityStructures.IsContinuousRandomModelWithFieldsOn Z₁ S)
    (hZ₂ : RegularityStructures.IsContinuousRandomModelWithFieldsOn Z₂ S) (γ : ℝ) :
    Measurable (fun ω => (Z₁ ω).gammaDiffNormOn (Z₂ ω) γ S) :=
  hZ₁.1.measurable_gammaDiffNormOn hZ₂.1 γ

end RegularityStructures

end
