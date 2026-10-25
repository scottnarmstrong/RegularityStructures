/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergenceNoiseMoments
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Almost-sure integrability of the exponentially weighted past

The massive kernel decays exponentially into the past. Joint measurability and the uniform
first moment of the forcing show that this remote-past majorant is integrable almost surely.
This is an input to the pathwise construction of the stationary linear field, for arbitrary
regularised-noise versions.
-/

@[expose] public noncomputable section

open MeasureTheory Real Set

namespace RegularityStructures.Phi43

def stochasticHeatPastWeight (T : ℝ) (z : SpaceTime) : ℝ :=
  (Iic T).indicator exp z.1

theorem measurable_stochasticHeatPastWeight (T : ℝ) :
    Measurable (stochasticHeatPastWeight T) :=
  (measurable_exp.indicator measurableSet_Iic).comp measurable_fst

theorem stochasticHeatPastWeight_nonneg (T : ℝ) (z : SpaceTime) :
    0 ≤ stochasticHeatPastWeight T z := by
  exact Set.indicator_nonneg (fun _ _ => exp_nonneg _) _

theorem integrable_stochasticHeatPastWeight (T : ℝ) :
    Integrable (stochasticHeatPastWeight T) := by
  have ht : Integrable ((Iic T).indicator exp) :=
    (integrableOn_exp_Iic T).integrable_indicator measurableSet_Iic
  exact ht.comp_fst (volume : Measure Torus3)

theorem integrable_regularisedNoise_past_product
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    (ξ : Ω → SpaceTime → ℝ) (hξ : IsRegularisedNoise P W ρ ε ξ) (T : ℝ) :
    Integrable (fun q : SpaceTime × Ω => stochasticHeatPastWeight T q.1 * ξ q.2 q.1)
      ((volume : Measure SpaceTime).prod P) := by
  let : IsProbabilityMeasure P := hW.isProbabilityMeasure
  obtain ⟨C, _hC, hbound⟩ := regularisedNoise_first_moment_bound_uniform ρ hρ hε
  have hξm := regularisedNoise_measurable_uncurry P W ρ ε ξ hξ
  have hFm : Measurable (fun q : SpaceTime × Ω => stochasticHeatPastWeight T q.1 * ξ q.2 q.1) :=
    ((measurable_stochasticHeatPastWeight T).comp measurable_fst).mul (hξm.comp measurable_swap)
  apply (integrable_prod_iff hFm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [] with z
    exact ((regularisedNoise_memLp_two hW ρ hρ hε ξ hξ z).integrable (by norm_num)).const_mul _
  · apply ((integrable_stochasticHeatPastWeight T).mul_const C).mono'
      hFm.aestronglyMeasurable.norm.integral_prod_right'
    filter_upwards [] with z
    rw [Real.norm_of_nonneg (integral_nonneg fun ω => norm_nonneg _)]
    calc
      _ = stochasticHeatPastWeight T z * ∫ ω, |ξ ω z| ∂P := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (stochasticHeatPastWeight_nonneg T z)]
      _ ≤ stochasticHeatPastWeight T z * C :=
        mul_le_mul_of_nonneg_left (hbound hW ξ hξ z) (stochasticHeatPastWeight_nonneg T z)

theorem regularisedNoise_weighted_past_integrable_ae
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    (ξ : Ω → SpaceTime → ℝ) (hξ : IsRegularisedNoise P W ρ ε ξ) (T : ℝ) :
    ∀ᵐ ω ∂P, Integrable (fun z : SpaceTime => stochasticHeatPastWeight T z * |ξ ω z|) := by
  let : IsProbabilityMeasure P := hW.isProbabilityMeasure
  have hi := integrable_regularisedNoise_past_product hW ρ hρ hε ξ hξ T
  filter_upwards [hi.prod_left_ae] with ω hω
  apply hω.norm.congr
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (stochasticHeatPastWeight_nonneg T z)]

theorem regularisedNoise_weighted_past_integrable_all_nat_ae
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    (ξ : Ω → SpaceTime → ℝ) (hξ : IsRegularisedNoise P W ρ ε ξ) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, Integrable
      (fun z : SpaceTime => stochasticHeatPastWeight (n : ℝ) z * |ξ ω z|) :=
  ae_all_iff.mpr fun n => regularisedNoise_weighted_past_integrable_ae hW ρ hρ hε ξ hξ n

end RegularityStructures.Phi43

end
