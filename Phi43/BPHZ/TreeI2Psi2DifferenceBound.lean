/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2DifferenceMean

/-!
# Almost-everywhere positivity for the difference diagrams of `I(Ψ²) Ψ²`

`ae_prod_pos_i2Psi2_diff`: for fixed points `y, y'`, almost every pair `(w, w')` of integration
variables has the five positive parabolic distances `s(w' - w)`, `s(y' - w)`, `s(y - w')`,
`s(y - w)`, `s(y' - w')` used by the diagram bounds for the covariance of the difference of two
fields of `I(Ψ²) Ψ²` ([Hai14, (10.3)]). It is used for the bound with two mollifiers
(`Phi43.BPHZ.TreeI2Psi2CrossBound`).
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- Almost every `(w, w')` has the five positivity properties used by the diagram bounds. -/
theorem ae_prod_pos_i2Psi2_diff (y y' : SpaceTime) :
    ∀ᵐ q : SpaceTime × SpaceTime ∂(volume.prod volume), 0 < torusParabolicSize (q.2 - q.1) ∧
      0 < torusParabolicSize (y' - q.1) ∧ 0 < torusParabolicSize (y - q.2) ∧
      0 < torusParabolicSize (y - q.1) ∧ 0 < torusParabolicSize (y' - q.2) := by
  have hm := Phi43.measurable_torusParabolicSize
  set S : Set (SpaceTime × SpaceTime) := {q | 0 < torusParabolicSize (q.2 - q.1) ∧
      0 < torusParabolicSize (y' - q.1) ∧ 0 < torusParabolicSize (y - q.2) ∧
      0 < torusParabolicSize (y - q.1) ∧ 0 < torusParabolicSize (y' - q.2)} with hSdef
  have hS : MeasurableSet S :=
    (measurableSet_lt measurable_const (hm.comp (measurable_snd.sub measurable_fst))).inter
      ((measurableSet_lt measurable_const (hm.comp (measurable_const.sub measurable_fst))).inter
        ((measurableSet_lt measurable_const (hm.comp (measurable_const.sub measurable_snd))).inter
          ((measurableSet_lt measurable_const (hm.comp (measurable_const.sub measurable_fst))).inter
            (measurableSet_lt measurable_const (hm.comp (measurable_const.sub measurable_snd))))))
  have hne : ∀ a : SpaceTime, ∀ᵐ z : SpaceTime ∂volume, z ≠ a := fun a =>
    @Measure.ae_ne SpaceTime _ volume (Measure.IsAddHaarMeasure.nullSingletonClass volume) a
  change ∀ᵐ q : SpaceTime × SpaceTime ∂(volume.prod volume), q ∈ S
  rw [Measure.ae_prod_mem_iff_ae_ae_mem hS]
  filter_upwards [hne y', hne y] with w hw1 hw2
  filter_upwards [hne w, hne y, hne y'] with w' h1 h2 h3
  exact ⟨torusParabolicSize_pos_of_ne_zero (sub_ne_zero.2 h1),
    torusParabolicSize_pos_of_ne_zero (sub_ne_zero.2 (Ne.symm hw1)),
    torusParabolicSize_pos_of_ne_zero (sub_ne_zero.2 (Ne.symm h2)),
    torusParabolicSize_pos_of_ne_zero (sub_ne_zero.2 (Ne.symm hw2)),
    torusParabolicSize_pos_of_ne_zero (sub_ne_zero.2 (Ne.symm h3))⟩

end RegularityStructures.Phi43

end
