/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Constants.Finite
import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Phi43.Stochastic.StochasticHeatConvergenceMoments

/-!
# The measurable `L²` input for the heat-smoothed size estimate

The spatially heat-averaged kernel is a parameter integral over the compact torus.  Consequently
it is continuous in the space-time variable whenever the mollified kernel is continuous.  This
file supplies that regularity and packages the Gaussian second-moment estimate from the explicit
stochastic-Fubini data in `StochasticHeatConvergenceS1`.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

theorem continuous_stochasticHeatKernel
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) {ε s : ℝ}
    (hε : 0 < ε) (hs : 0 < s) (z : SpaceTime) :
    Continuous (stochasticHeatKernel ρ ε s z) := by
  obtain ⟨hG, _, _⟩ := mollifiedKernel_facts ρ hρ hε
  let f : SpaceTime → Torus3 → ℝ := fun w y =>
    heatKernel s y * mollifiedKernel ρ ε ((z.1, z.2 - y) - w)
  have hf : Continuous f.uncurry := by
    have hheat : Continuous (heatKernel s) := continuous_heatKernel_fixed hs
    have harg : Continuous (fun p : SpaceTime × Torus3 =>
        ((z.1, z.2 - p.2) - p.1)) := by
      fun_prop
    exact (hheat.comp continuous_snd).mul (hG.comp harg)
  have hparam : Continuous (fun w : SpaceTime => ∫ y : Torus3, f w y) :=
    by
      simpa only [Measure.restrict_univ] using
        (continuous_parametric_integral_of_continuous hf isCompact_univ)
  change Continuous (fun w : SpaceTime =>
    ∫ y : Torus3, heatKernel s y *
      mollifiedKernel ρ ε ((z.1, z.2 - y) - w))
  exact hparam

theorem memLp_stochasticHeatKernel_of_integrable_square
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) {ε s : ℝ}
    (hε : 0 < ε) (hs : 0 < s) (z : SpaceTime)
    (haverage : Integrable (fun w : SpaceTime =>
      stochasticHeatKernel ρ ε s z w ^ 2)) :
    MemLp (stochasticHeatKernel ρ ε s z) 2 := by
  apply (memLp_two_iff_integrable_sq
    (continuous_stochasticHeatKernel ρ hρ hε hs z).measurable.aestronglyMeasurable).2
  exact haverage

theorem integrable_stochasticHeatKernel_square_of_mollifiedKernel_facts
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) {ε s : ℝ}
    (hε : 0 < ε) (hs : 0 < s) (z : SpaceTime) :
    Integrable (fun w : SpaceTime =>
      stochasticHeatKernel ρ ε s z w ^ 2) := by
  obtain ⟨hGcont, hGint, B, hGB⟩ := mollifiedKernel_facts ρ hρ hε
  let D : ℝ := max B 0
  have hD : 0 ≤ D := le_max_right B 0
  have hGBD : ∀ u : SpaceTime, |mollifiedKernel ρ ε u| ≤ D := by
    intro u
    exact (hGB u).trans (le_max_left B 0)
  let H : Torus3 × SpaceTime → ℝ := fun q =>
    heatKernel s q.1 * mollifiedKernel ρ ε ((z.1, z.2 - q.1) - q.2)
  have hHmeas : Measurable H := by
    dsimp [H]
    have harg : Measurable (fun q : Torus3 × SpaceTime =>
        ((z.1, z.2 - q.1) - q.2)) := by
      fun_prop
    exact (measurable_heatKernel_fixed s).comp measurable_fst |>.mul
      (hGcont.measurable.comp harg)
  have hHprod : Integrable H := by
    apply (integrable_prod_iff hHmeas.aestronglyMeasurable).2
    constructor
    · filter_upwards [] with y
      have hFy : Integrable (fun w : SpaceTime =>
          mollifiedKernel ρ ε ((z.1, z.2 - y) - w)) :=
        integrable_comp_sub_left_spaceTime hGint (z.1, z.2 - y)
      have hbound : ∀ᵐ w : SpaceTime, ‖heatKernel s y‖ ≤ |heatKernel s y| :=
        Filter.Eventually.of_forall fun w => by
          rw [Real.norm_eq_abs]
      have hi := hFy.bdd_mul measurable_const.aestronglyMeasurable hbound
      simpa [H] using hi
    · let I : ℝ := ∫ u : SpaceTime, |mollifiedKernel ρ ε u|
      have hinner : ∀ y : Torus3, ∫ w : SpaceTime, ‖H (y, w)‖ =
          heatKernel s y * I := by
        intro y
        have hshift := integral_comp_sub_left_spaceTime
          (fun u : SpaceTime => |mollifiedKernel ρ ε u|) (z.1, z.2 - y)
        calc
          ∫ w : SpaceTime, ‖H (y, w)‖ =
              ∫ w : SpaceTime, heatKernel s y *
                |mollifiedKernel ρ ε ((z.1, z.2 - y) - w)| := by
            apply integral_congr_ae
            filter_upwards [] with w
            dsimp [H]
            rw [abs_mul, abs_of_nonneg (heatKernel_nonneg hs y)]
          _ = heatKernel s y *
                (∫ w : SpaceTime,
                  |mollifiedKernel ρ ε ((z.1, z.2 - y) - w)|) :=
            integral_const_mul _ _
          _ = heatKernel s y * I := by
            rw [hshift]
      have hinner_int : Integrable (fun y : Torus3 =>
          heatKernel s y * I) := by
        exact (integrable_heatKernel_fixed hs).mul_const I
      exact hinner_int.congr (Filter.Eventually.of_forall fun y =>
        (hinner y).symm)
  have hAint : Integrable (fun w : SpaceTime =>
      ∫ y : Torus3, H (y, w)) := hHprod.integral_prod_right
  have hAw : ∀ w : SpaceTime, |∫ y : Torus3, H (y, w)| ≤ D := by
    intro w
    have hslice : Integrable (fun y : Torus3 => H (y, w)) := by
      have hp := integrable_heatKernel_fixed hs
      have hbound : ∀ᵐ y : Torus3, ‖mollifiedKernel ρ ε
          ((z.1, z.2 - y) - w)‖ ≤ D :=
        Filter.Eventually.of_forall fun y => by
          simpa only [Real.norm_eq_abs] using hGBD ((z.1, z.2 - y) - w)
      have harg : Measurable (fun y : Torus3 =>
          ((z.1, z.2 - y) - w)) := by
        fun_prop
      have hFmeas : AEStronglyMeasurable (fun y : Torus3 =>
          mollifiedKernel ρ ε ((z.1, z.2 - y) - w)) :=
        (hGcont.measurable.comp harg).aestronglyMeasurable
      simpa [H] using hp.mul_bdd hFmeas hbound
    have hmajor : Integrable (fun y : Torus3 => D * heatKernel s y) :=
      (integrable_heatKernel_fixed hs).const_mul D
    have hnorm := norm_integral_le_of_norm_le
      (f := fun y : Torus3 => H (y, w)) hmajor
      (Filter.Eventually.of_forall fun y => by
        change |heatKernel s y *
          mollifiedKernel ρ ε ((z.1, z.2 - y) - w)| ≤ D * heatKernel s y
        rw [abs_mul, abs_of_nonneg (heatKernel_nonneg hs y)]
        exact (mul_le_mul_of_nonneg_left
          (hGBD ((z.1, z.2 - y) - w)) (heatKernel_nonneg hs y)).trans_eq (by ring))
    rw [Real.norm_eq_abs] at hnorm
    calc
      |∫ y : Torus3, H (y, w)| ≤ ∫ y : Torus3, D * heatKernel s y := hnorm
      _ = D * ∫ y : Torus3, heatKernel s y := integral_const_mul _ _
      _ = D := by rw [integral_heatKernel hs, mul_one]
  have hAsq : Integrable (fun w : SpaceTime =>
      (∫ y : Torus3, H (y, w)) ^ 2) := by
    have hmul := hAint.mul_bdd hAint.aestronglyMeasurable
      (Filter.Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs]
        exact hAw w)
    convert hmul using 1
    funext w
    ring
  change Integrable (fun w : SpaceTime =>
    (∫ y : Torus3, heatKernel s y *
      mollifiedKernel ρ ε ((z.1, z.2 - y) - w)) ^ 2)
  exact hAsq

end RegularityStructures.Phi43

end
