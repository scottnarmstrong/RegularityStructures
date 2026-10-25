/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Order.CompletePartialOrder
public import Phi43.Stochastic.StochasticHeatConvergenceS4
public import RegularityStructures.Probability.KolmogorovChentsovHolderBesov

/-!
# Bundled compact-time Besov paths

Restriction and the canonical embedding turn the continuous spatial versions into genuine
random variables in the complete path space `C([0,1], HolderBesov η)`. The parameter `T`
rescales the unit interval to `[0,T]`. No choice of pointwise representatives is made here.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal

namespace RegularityStructures.Phi43

instance (η : NegExponent) : SeparableSpace (HolderBesov η) := by
  have hd : DenseRange (toHolderBesov η) := by
    have hr : Set.range (toHolderBesov η) =
        Set.range ((↑) : HolderBesovPre η → HolderBesov η) := rfl
    intro y
    rw [hr]
    exact (UniformSpace.Completion.denseRange_coe (α := HolderBesovPre η)) y
  exact hd.separableSpace (toHolderBesov_lipschitzWith η).continuous

/-- A continuous spatial path, restricted to `[0,T]` and embedded into `𝒞^η`. -/
def stochasticHeatBesovPath (η : NegExponent) (T : ℝ)
    (f : C(ℝ, C(Torus3, ℝ))) : C(UnitInterval, HolderBesov η) :=
  (⟨toHolderBesov η, (toHolderBesov_lipschitzWith η).continuous⟩ :
    C(C(Torus3, ℝ), HolderBesov η)).comp
      (f.comp ⟨fun u : UnitInterval => T * (u : ℝ), continuous_const.mul continuous_subtype_val⟩)

theorem continuous_stochasticHeatBesovPath (η : NegExponent) (T : ℝ) :
    Continuous (stochasticHeatBesovPath η T) :=
  (ContinuousMap.continuous_postcomp
    ⟨toHolderBesov η, (toHolderBesov_lipschitzWith η).continuous⟩).comp
      (ContinuousMap.continuous_precomp
        ⟨fun u : UnitInterval => T * (u : ℝ), continuous_const.mul continuous_subtype_val⟩)

theorem enorm_stochasticHeatBesovPath (η : NegExponent) (T : ℝ)
    (f : C(ℝ, C(Torus3, ℝ))) :
    ‖stochasticHeatBesovPath η T f‖ₑ =
      ⨆ u : UnitInterval, holderBesovENorm η (f (T * u)) := by
  rw [ContinuousMap.enorm_eq_iSup_enorm]
  exact iSup_congr fun u => enorm_toHolderBesov η _

theorem enorm_stochasticHeatBesovPath_sub (η : NegExponent) (T : ℝ)
    (f g : C(ℝ, C(Torus3, ℝ))) :
    ‖stochasticHeatBesovPath η T f - stochasticHeatBesovPath η T g‖ₑ =
      ⨆ u : UnitInterval, holderBesovENorm η (f (T * u) - g (T * u)) := by
  rw [ContinuousMap.enorm_eq_iSup_enorm]
  apply iSup_congr
  intro u
  change ‖toHolderBesov η (f (T * u)) - toHolderBesov η (g (T * u))‖ₑ = _
  rw [← toHolderBesov_sub, enorm_toHolderBesov]

end RegularityStructures.Phi43

end
