/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergenceBareResolvent

/-!
# The causal kernel after spatial heat regularisation

`bareHeatRegularisedKernel s` is the spatial heat convolution of the massive kernel,
with the causal cutoff retained. Its covariance is the resolvent computed in the preceding
module. This is the square-integrable deterministic kernel used before mollification.
-/

@[expose] public noncomputable section

open MeasureTheory Real Set

namespace RegularityStructures.Phi43

def bareHeatRegularisedKernel (s : ℝ) (z : SpaceTime) : ℝ :=
  if 0 < z.1 then exp (-z.1) * heatKernel (s + z.1) z.2 else 0

theorem measurable_bareHeatRegularisedKernel (s : ℝ) :
    Measurable (bareHeatRegularisedKernel s) := by
  apply Measurable.ite (measurableSet_lt measurable_const measurable_fst)
  · exact measurable_fst.neg.exp.mul
      (measurable_heatKernel.comp ((measurable_const.add measurable_fst).prodMk measurable_snd))
  · exact measurable_const

theorem bareHeatRegularisedKernel_nonneg {s : ℝ} (hs : 0 < s) (z : SpaceTime) :
    0 ≤ bareHeatRegularisedKernel s z := by
  unfold bareHeatRegularisedKernel
  split_ifs with hz
  · exact mul_nonneg (exp_nonneg _) (heatKernel_nonneg (add_pos hs hz) _)
  · exact le_rfl

theorem bareHeatRegularisedKernel_eq_spatial_integral {s : ℝ} (hs : 0 < s)
    (z : SpaceTime) :
    bareHeatRegularisedKernel s z =
      ∫ y : Torus3, heatKernel s y * massiveHeatKernel (z.1, z.2 - y) := by
  by_cases hz : 0 < z.1
  · rw [integral_heatKernel_mul_massiveHeatKernel_torus hs hz]
    simp only [bareHeatRegularisedKernel, hz, ite_true]
  · simp only [bareHeatRegularisedKernel, massiveHeatKernel, hz, ite_false, mul_zero,
      integral_zero]

private theorem bareHeatRegularisedKernel_covariance_indicator
    {s t : ℝ} (ht : 0 ≤ t) (x : Torus3) :
    (fun w : SpaceTime => bareHeatRegularisedKernel s ((t, x) + w) *
      bareHeatRegularisedKernel s w) =
    (Ioi (0 : ℝ) ×ˢ (univ : Set Torus3)).indicator (fun p : ℝ × Torus3 =>
      (exp (-(|t| + p.1)) * heatKernel (s + |t| + p.1) (x + p.2)) *
        (exp (-p.1) * heatKernel (s + p.1) p.2)) := by
  funext w
  by_cases hw : 0 < w.1
  · have htw : 0 < t + w.1 := add_pos_of_nonneg_of_pos ht hw
    simp only [bareHeatRegularisedKernel, Prod.fst_add, Prod.snd_add, htw, hw, ite_true,
      indicator_apply, mem_prod, mem_Ioi, mem_univ, and_true, abs_of_nonneg ht]
    simp only [add_assoc]
  · simp only [bareHeatRegularisedKernel, hw, ite_false, mul_zero,
      indicator_apply, mem_prod, mem_Ioi, mem_univ, and_true]

theorem integrable_bareHeatRegularisedKernel_covariance
    {s t : ℝ} (hs : 0 < s) (ht : 0 ≤ t) (x : Torus3) :
    Integrable (fun w : SpaceTime => bareHeatRegularisedKernel s ((t, x) + w) *
      bareHeatRegularisedKernel s w) := by
  have hi := integrable_heatRegularised_massive_covariance_product hs t x
  rw [Measure.restrict_prod_eq_prod_univ] at hi
  rw [bareHeatRegularisedKernel_covariance_indicator ht]
  exact (integrable_indicator_iff (measurableSet_Ioi.prod MeasurableSet.univ)).mpr hi

theorem integral_bareHeatRegularisedKernel_covariance_eq_resolvent
    {s t : ℝ} (hs : 0 < s) (ht : 0 ≤ t) (x : Torus3) :
    ∫ w : SpaceTime, bareHeatRegularisedKernel s ((t, x) + w) *
        bareHeatRegularisedKernel s w =
      exp (2 * s) / 2 *
        ∫ u : ℝ in Ioi (2 * s + |t|), massiveHeatKernel (u, x) := by
  rw [bareHeatRegularisedKernel_covariance_indicator ht,
    integral_indicator (measurableSet_Ioi.prod MeasurableSet.univ)]
  change (∫ w : ℝ × Torus3,
    (exp (-(|t| + w.1)) * heatKernel (s + |t| + w.1) (x + w.2)) *
      (exp (-w.1) * heatKernel (s + w.1) w.2)
    ∂((volume : Measure ℝ).prod (volume : Measure Torus3)).restrict (Ioi 0 ×ˢ univ)) = _
  rw [← Measure.restrict_prod_eq_prod_univ,
    integral_prod _ (integrable_heatRegularised_massive_covariance_product hs t x)]
  exact integral_heatRegularised_massive_covariance_eq_resolvent hs t x

end RegularityStructures.Phi43

end
