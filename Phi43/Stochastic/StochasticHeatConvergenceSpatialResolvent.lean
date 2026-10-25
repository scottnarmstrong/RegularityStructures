/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergenceSpatialLipschitz
public import Phi43.Stochastic.StochasticHeatConvergenceResolventBounds

/-!
# Spatial modulus of the massive-kernel time tail

Integrating the global spatial derivative bound against the massive exponential yields a spatial
Lipschitz modulus for the time-tail resolvent. Its constant is independent of the lower endpoint and
spatial displacement; this is the bare covariance input to the space-time increment bound.
-/

@[expose] public noncomputable section

open MeasureTheory Real Set

namespace RegularityStructures.Phi43

theorem massiveHeatKernel_time_tail_spatial_modulus :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a : ℝ}, 0 < a → ∀ x : Torus3,
      |(∫ t : ℝ in Ioi a, massiveHeatKernel (t, x)) -
          ∫ t : ℝ in Ioi a, massiveHeatKernel (t, 0)| ≤
        C * (a⁻¹ + 1) * torusSpatialNorm x := by
  obtain ⟨C, hC, hbound⟩ := heatKernel_spatial_modulus_uniform_time
  refine ⟨C, hC, ?_⟩
  intro a ha x
  have hpowi := integrableOn_Ioi_rpow_of_lt (by norm_num : -(2 : ℝ) < -1) ha
  have hexpi := integrableOn_exp_neg_Ioi a
  have hexpm : Measurable (fun t : ℝ => exp (-t)) := measurable_id.neg.exp
  have hexpbound : ∀ᵐ t : ℝ ∂volume.restrict (Ioi a), ‖exp (-t)‖ ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : a < t := ht
    rw [Real.norm_of_nonneg (exp_nonneg _), exp_le_one_iff]
    linarith only [ha, ht0]
  have hi2e : IntegrableOn (fun t : ℝ => exp (-t) * t ^ (-(2 : ℝ))) (Ioi a) := by
    apply (hpowi.mul_bdd hexpm.aestronglyMeasurable hexpbound).congr
    filter_upwards [] with t
    exact mul_comm _ _
  have hsum : IntegrableOn (fun t : ℝ => exp (-t) * (t ^ (-(2 : ℝ)) + 1)) (Ioi a) := by
    apply (hi2e.add hexpi).congr
    filter_upwards [] with t
    simp only [Pi.add_apply]
    ring
  have hint : (∫ t : ℝ in Ioi a, exp (-t) * (t ^ (-(2 : ℝ)) + 1)) ≤ a⁻¹ + 1 := by
    calc
      _ = (∫ t : ℝ in Ioi a, exp (-t) * t ^ (-(2 : ℝ))) +
          ∫ t : ℝ in Ioi a, exp (-t) := by
        rw [← integral_add hi2e hexpi]
        apply integral_congr_ae
        filter_upwards [] with t
        ring
      _ ≤ (∫ t : ℝ in Ioi a, t ^ (-(2 : ℝ))) + exp (-a) := by
        rw [integral_exp_neg_Ioi]
        refine add_le_add ?_ le_rfl
        apply integral_mono_ae hi2e hpowi
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : 0 < t := ha.trans ht
        have he : exp (-t) ≤ 1 := exp_le_one_iff.mpr (neg_nonpos.mpr ht0.le)
        simpa only [mul_comm] using mul_le_of_le_one_right (rpow_nonneg ht0.le _) he
      _ = a⁻¹ + exp (-a) := by
        rw [integral_Ioi_rpow_of_lt (by norm_num : -(2 : ℝ) < -1) ha]
        norm_num [rpow_neg_one]
      _ ≤ a⁻¹ + 1 := add_le_add le_rfl (exp_le_one_iff.mpr (neg_nonpos.mpr ha.le))
  have hnorm := norm_integral_le_of_norm_le
    (f := fun t : ℝ => massiveHeatKernel (t, x) - massiveHeatKernel (t, 0))
    (hsum.const_mul (C * torusSpatialNorm x)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := ha.trans ht
      rw [Real.norm_eq_abs]
      simp only [massiveHeatKernel, ht0, ite_true]
      rw [← mul_sub, abs_mul, abs_of_nonneg (exp_nonneg _)]
      calc
        _ ≤ exp (-t) * (C * (t ^ (-(2 : ℝ)) + 1) * torusSpatialNorm x) :=
          mul_le_mul_of_nonneg_left (hbound ht0 x) (exp_nonneg _)
        _ = (C * torusSpatialNorm x) * (exp (-t) * (t ^ (-(2 : ℝ)) + 1)) := by ring)
  calc
    _ = ‖∫ t : ℝ in Ioi a, massiveHeatKernel (t, x) - massiveHeatKernel (t, 0)‖ := by
      rw [integral_sub (integrableOn_massiveHeatKernel_time_tail ha x)
        (integrableOn_massiveHeatKernel_time_tail ha 0), Real.norm_eq_abs]
    _ ≤ ∫ t : ℝ in Ioi a,
        (C * torusSpatialNorm x) * (exp (-t) * (t ^ (-(2 : ℝ)) + 1)) := hnorm
    _ = (C * torusSpatialNorm x) *
        ∫ t : ℝ in Ioi a, exp (-t) * (t ^ (-(2 : ℝ)) + 1) := integral_const_mul _ _
    _ ≤ (C * torusSpatialNorm x) * (a⁻¹ + 1) :=
      mul_le_mul_of_nonneg_left hint (mul_nonneg hC (torusSpatialNorm_nonneg x))
    _ = C * (a⁻¹ + 1) * torusSpatialNorm x := by ring

end RegularityStructures.Phi43

end
