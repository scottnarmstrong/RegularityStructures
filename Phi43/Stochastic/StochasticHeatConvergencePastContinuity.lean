/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergenceKernelContinuity
public import Phi43.Stochastic.StochasticHeatConvergencePast
import RegularityStructures.Torus.KernelBoundsLargeTime
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Continuity of the remote-past convolution

An exponentially weighted integrable forcing gives a continuous remote-past contribution to
the massive heat convolution. The gap to the past cutoff keeps the heat kernel away from its
singularity; exponential decay, from equation (2.2) of the statement, supplies domination.
-/

public section

open MeasureTheory Real Set
open scoped Topology

namespace RegularityStructures.Phi43

theorem integrableOn_massiveHeatKernel_past_product
    {g : SpaceTime → ℝ} (hg : Measurable g) {a : ℝ}
    (hi : IntegrableOn (fun w : SpaceTime => exp w.1 * |g w|)
      {w : SpaceTime | w.1 ≤ a})
    {z : SpaceTime} (hz : a + 1 ≤ z.1) :
    IntegrableOn (fun w : SpaceTime => massiveHeatKernel (z - w) * g w)
      {w : SpaceTime | w.1 ≤ a} := by
  obtain ⟨C, hC⟩ := massiveHeatKernel_exponential_bound
  apply (hi.const_mul (C * exp (-z.1))).mono'
    (((measurable_massiveHeatKernel.comp (measurable_const.sub measurable_id)).mul hg).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem (measurableSet_le measurable_fst measurable_const)] with w hw
  change ‖massiveHeatKernel (z - w) * g w‖ ≤ (C * exp (-z.1)) * (exp w.1 * |g w|)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (massiveHeatKernel_nonneg _)]
  calc
    massiveHeatKernel (z - w) * |g w| ≤ (C * exp (-(z - w).1)) * |g w| :=
      mul_le_mul_of_nonneg_right (hC _ (by change 1 ≤ z.1 - w.1; linarith only [hw, hz]))
        (abs_nonneg _)
    _ = (C * exp (-z.1)) * (exp w.1 * |g w|) := by
      change (C * exp (-(z.1 - w.1))) * |g w| = _
      rw [neg_sub, sub_eq_neg_add, exp_add]
      ring

theorem continuousAt_massiveHeatKernel_past_convolution
    {g : SpaceTime → ℝ} (hg : Measurable g) {a : ℝ}
    (hi : IntegrableOn (fun w : SpaceTime => exp w.1 * |g w|)
      {w : SpaceTime | w.1 ≤ a})
    {z : SpaceTime} (hz : a + 2 ≤ z.1) :
    ContinuousAt (fun p : SpaceTime =>
      ∫ w in {w : SpaceTime | w.1 ≤ a}, massiveHeatKernel (p - w) * g w) z := by
  obtain ⟨C₀, hC₀⟩ := massiveHeatKernel_exponential_bound
  let C := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  have hG : ∀ p : SpaceTime, 1 ≤ p.1 → massiveHeatKernel p ≤ C * exp (-p.1) := by
    intro p hp
    exact (hC₀ p hp).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (exp_nonneg _))
  have hpast : MeasurableSet {w : SpaceTime | w.1 ≤ a} := measurableSet_le measurable_fst measurable_const
  apply continuousAt_of_dominated (bound := fun w : SpaceTime =>
    (C * exp (1 - z.1)) * (exp w.1 * |g w|))
  · exact Filter.Eventually.of_forall fun p =>
      ((measurable_massiveHeatKernel.comp (measurable_const.sub measurable_id)).mul hg).aestronglyMeasurable
  · filter_upwards [continuousAt_fst.preimage_mem_nhds (Ioi_mem_nhds (show z.1 - 1 < z.1 by linarith))]
      with p hp
    filter_upwards [ae_restrict_mem hpast] with w hw
    have hp' : z.1 - 1 < p.1 := hp
    have hgap : 1 ≤ (p - w).1 := by
      change 1 ≤ p.1 - w.1
      linarith only [hp', hw, hz]
    have hnonneg : 0 ≤ massiveHeatKernel (p - w) := massiveHeatKernel_nonneg _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnonneg]
    calc
      massiveHeatKernel (p - w) * |g w| ≤ (C * exp (-(p - w).1)) * |g w| :=
        mul_le_mul_of_nonneg_right (hG _ hgap) (abs_nonneg _)
      _ ≤ (C * exp (1 - z.1 + w.1)) * |g w| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        apply mul_le_mul_of_nonneg_left _ hC
        apply exp_le_exp.mpr
        change -(p.1 - w.1) ≤ 1 - z.1 + w.1
        linarith only [hp']
      _ = (C * exp (1 - z.1)) * (exp w.1 * |g w|) := by rw [exp_add]; ring
  · exact hi.const_mul _
  · filter_upwards [ae_restrict_mem hpast] with w hw
    have hgap : 0 < (z - w).1 := by
      change 0 < z.1 - w.1
      linarith only [hw, hz]
    exact ((continuousAt_massiveHeatKernel_time_ne_zero hgap.ne').comp
      (f := fun p : SpaceTime => p - w) (continuousAt_id.sub continuousAt_const)).mul
      continuousAt_const

end RegularityStructures.Phi43

end
