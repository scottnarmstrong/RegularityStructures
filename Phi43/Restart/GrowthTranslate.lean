/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Translate.Model
public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Analysis.Semigroup.Weighted.Defs

/-!
# Translation covariance of the weighted growth hypotheses

A translated model `M.translate a` has the growth model of `M` with the translated weights
`z ↦ ρ (z + a)` (the parabolic scale distance is translation invariant).
-/

public section

open MeasureTheory

namespace RegularityStructures

namespace Model

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  {M : Model 𝒯 parabolicSemigroup} {γ C C' p q : ℝ} {ρP ρG : ParabolicSpace → ℝ}

theorem isModerateWeight_translate {ρ : ParabolicSpace → ℝ}
    (h : parabolicSemigroup.IsModerateWeight ρ p) (a : ParabolicSpace) :
    parabolicSemigroup.IsModerateWeight (fun z => ρ (z + a)) p where
  one_le x := h.one_le _
  measurable := h.measurable.comp (measurable_id.add_const a)
  nonneg_exp := h.nonneg_exp
  le y z := by
    have := h.le (y + a) (z + a)
    rwa [parabolicSemigroup_scaleDist_translate a y z] at this

/-- **Growth models are translation covariant.** -/
theorem GrowthModel.translate (G : M.GrowthModel γ C C' ρP ρG p q) (a : ParabolicSpace) :
    (M.translate a).GrowthModel γ C C' (fun z => ρP (z + a)) (fun z => ρG (z + a)) p q where
  pos := G.pos
  moderateP := isModerateWeight_translate G.moderateP a
  moderateG := isModerateWeight_translate G.moderateG a
  nonnegG := G.nonnegG
  piBound i hi t ht x := G.piBound i hi t ht (x + a)
  gammaBound i j hi hji x y := by
    have := G.gammaBound i j hi hji (x + a) (y + a)
    simpa only [gammaMap_translate, parabolicSemigroup_scaleDist_translate] using this
  piBound_nonneg := G.piBound_nonneg

end Model

end RegularityStructures

end
