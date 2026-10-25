/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HeatKernelRegularity
public import RegularityStructures.Probability.SpaceTimeMeasure
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Integrability of the massive heat kernel

The nonnegative space-time kernel has mass one: the spatial mass is the Gaussian normalization and
the remaining time integral is the exponential integral on `(0, ∞)`.
-/

@[expose] public noncomputable section

open MeasureTheory Real Set

namespace RegularityStructures

theorem integrable_heatKernel_fixed {t : ℝ} (ht : 0 < t) :
    Integrable (heatKernel t) := by
  rcases bounded_heatKernel ht with ⟨C, hC⟩
  refine Integrable.of_bound (continuous_heatKernel_fixed ht).aestronglyMeasurable C ?_
  exact Filter.Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs] using hC x

theorem lintegral_heatKernel_fixed {t : ℝ} (ht : 0 < t) :
    ∫⁻ x : Torus3, ENNReal.ofReal (heatKernel t x) = 1 := by
  calc
    (∫⁻ x : Torus3, ENNReal.ofReal (heatKernel t x)) =
        ENNReal.ofReal (∫ x : Torus3, heatKernel t x) :=
      (ofReal_integral_eq_lintegral_ofReal (integrable_heatKernel_fixed ht)
        (Filter.Eventually.of_forall (heatKernel_nonneg ht))).symm
    _ = 1 := by rw [integral_heatKernel ht, ENNReal.ofReal_one]

def massiveTimeKernel (t : ℝ) : ℝ := if 0 < t then exp (-t) else 0

theorem integrable_massiveTimeKernel : Integrable massiveTimeKernel := by
  have h := (integrableOn_exp_neg_Ioi 0).integrable_indicator measurableSet_Ioi
  apply h.congr
  exact Filter.Eventually.of_forall fun t => by
    simp [massiveTimeKernel, Set.indicator]

theorem integral_massiveTimeKernel : ∫ t, massiveTimeKernel t = 1 := by
  rw [show massiveTimeKernel = (Set.Ioi (0 : ℝ)).indicator (fun t : ℝ => exp (-t)) by
    funext t
    simp [massiveTimeKernel, Set.indicator]]
  rw [integral_indicator measurableSet_Ioi, integral_exp_neg_Ioi_zero]

theorem lintegral_massiveTimeKernel :
    ∫⁻ t, ENNReal.ofReal (massiveTimeKernel t) = 1 := by
  calc
    (∫⁻ t, ENNReal.ofReal (massiveTimeKernel t)) =
        ENNReal.ofReal (∫ t, massiveTimeKernel t) :=
      (ofReal_integral_eq_lintegral_ofReal integrable_massiveTimeKernel
        (Filter.Eventually.of_forall fun t => by
          unfold massiveTimeKernel
          split_ifs <;> positivity)).symm
    _ = 1 := by rw [integral_massiveTimeKernel, ENNReal.ofReal_one]

theorem lintegral_massiveHeatKernel :
    ∫⁻ z : SpaceTime, ENNReal.ofReal (massiveHeatKernel z) = 1 := by
  have hprod :
      (∫⁻ z : SpaceTime, ENNReal.ofReal (massiveHeatKernel z)) =
        ∫⁻ t : ℝ, ∫⁻ x : Torus3, ENNReal.ofReal (massiveHeatKernel (t, x)) := by
    change (∫⁻ z : ℝ × Torus3,
      ENNReal.ofReal (massiveHeatKernel z) ∂((volume : Measure ℝ).prod volume)) = _
    rw [MeasureTheory.lintegral_prod]
    exact (measurable_massiveHeatKernel.ennreal_ofReal).aemeasurable
  rw [hprod]
  calc
    (∫⁻ t : ℝ, ∫⁻ x : Torus3, ENNReal.ofReal (massiveHeatKernel (t, x))) =
        ∫⁻ t : ℝ, ENNReal.ofReal (massiveTimeKernel t) := by
      apply lintegral_congr_ae
      filter_upwards [] with t
      by_cases ht : 0 < t
      · simp only [massiveHeatKernel, ht, ite_true, massiveTimeKernel]
        calc
          (∫⁻ x : Torus3, ENNReal.ofReal (exp (-t) * heatKernel t x)) =
              ∫⁻ x : Torus3,
                ENNReal.ofReal (exp (-t)) * ENNReal.ofReal (heatKernel t x) := by
            apply lintegral_congr
            intro x
            rw [ENNReal.ofReal_mul (exp_nonneg _)]
          _ = ENNReal.ofReal (exp (-t)) := by
            rw [lintegral_const_mul]
            · simp [lintegral_heatKernel_fixed ht]
            · exact (continuous_heatKernel_fixed ht).measurable.ennreal_ofReal
      · simp [massiveHeatKernel, ht, massiveTimeKernel]
    _ = 1 := lintegral_massiveTimeKernel

theorem integrable_massiveHeatKernel : Integrable massiveHeatKernel := by
  refine ⟨measurable_massiveHeatKernel.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  have hnorm :
      (∫⁻ z : SpaceTime, ENNReal.ofReal ‖massiveHeatKernel z‖) =
        ∫⁻ z : SpaceTime, ENNReal.ofReal (massiveHeatKernel z) := by
    apply lintegral_congr_ae
    filter_upwards [] with z
    rw [Real.norm_of_nonneg (massiveHeatKernel_nonneg z)]
  rw [hnorm, lintegral_massiveHeatKernel]
  exact ENNReal.one_lt_top

theorem integral_massiveHeatKernel : ∫ z : SpaceTime, massiveHeatKernel z = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall massiveHeatKernel_nonneg)
    integrable_massiveHeatKernel.aestronglyMeasurable]
  rw [lintegral_massiveHeatKernel]
  rfl

end RegularityStructures

end
