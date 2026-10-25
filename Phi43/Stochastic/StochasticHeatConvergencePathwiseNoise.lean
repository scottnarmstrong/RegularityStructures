/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergencePathwiseContinuity

/-!
# Pathwise continuity and joint measurability for arbitrary regularised noises

The stationary massive heat convolution of any `IsRegularisedNoise` is jointly measurable and has
continuous space-time paths almost surely. No choice of a canonical white-noise representative is
assumed. This supplies the continuous-function-valued carrier for the stationary linear field;
identification and uniform negative-Hölder moments are separate steps.

Source: the statement, equation (2.2) and the definition of the regularised noise.
-/

public noncomputable section

open MeasureTheory Real Set

namespace RegularityStructures.Phi43

theorem regularisedNoise_massiveHeatKernel_convolution_continuous_ae
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} (hW : IsWhiteNoise P W)
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    (ξ : Ω → SpaceTime → ℝ) (hξ : IsRegularisedNoise P W ρ ε ξ) :
    ∀ᵐ ω ∂P, Continuous (fun z : SpaceTime =>
      ∫ w : SpaceTime, massiveHeatKernel (z - w) * ξ ω w) := by
  filter_upwards [regularisedNoise_weighted_past_integrable_all_nat_ae hW ρ hρ hε ξ hξ]
    with ω hω
  apply continuous_massiveHeatKernel_convolution_of_weighted_past
    (Continuous.continuous_of_isSmoothOnSpaceTime (hξ.1 ω))
  intro a
  obtain ⟨n, hn⟩ := exists_nat_gt a
  apply (hω n).integrableOn.congr
  filter_upwards [ae_restrict_mem (measurableSet_le measurable_fst measurable_const)] with w hw
  rw [stochasticHeatPastWeight, indicator_of_mem (show w.1 ∈ Iic (n : ℝ) from hw.trans hn.le)]

theorem regularisedNoise_massiveHeatKernel_convolution_measurable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ}
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) {ε : ℝ}
    (ξ : Ω → SpaceTime → ℝ) (hξ : IsRegularisedNoise P W ρ ε ξ) :
    Measurable (fun q : Ω × SpaceTime =>
      ∫ w : SpaceTime, massiveHeatKernel (q.2 - w) * ξ q.1 w) := by
  have hξm := regularisedNoise_measurable_uncurry P W ρ ε ξ hξ
  have hF : Measurable (fun q : (Ω × SpaceTime) × SpaceTime =>
      massiveHeatKernel (q.1.2 - q.2) * ξ q.1.1 q.2) :=
    (measurable_massiveHeatKernel.comp
      ((measurable_snd.comp measurable_fst).sub measurable_snd)).mul
      (hξm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  exact hF.stronglyMeasurable.integral_prod_right'.measurable

end RegularityStructures.Phi43

end
