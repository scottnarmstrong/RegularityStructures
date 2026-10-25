/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergenceBareMollification
public import Phi43.Stochastic.StochasticHeatConvergenceYoungL2
public import Phi43.Torus.KernelBoundsConvolution
public import Phi43.Stochastic.StochasticHeatConvergenceMoments

/-!
# Uniform time increments for the mollified stochastic heat kernel

The bare-kernel time modulus survives mollification by the L¹--L² averaging inequality. The
resulting constants depend on the mollifier and the fractional exponent, and precede every
regularisation, heat, time and spatial variable. White-noise isometry gives the time-increment bound
for the canonical Gaussian field without any covariance-bound hypothesis.
-/

@[expose] public noncomputable section

open MeasureTheory Real

namespace RegularityStructures.Phi43

private theorem memLp_periodise_two_local
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) :
    MemLp (periodise ρ ε) 2 := by
  obtain ⟨B, hB⟩ := bounded_periodise ρ hρ hε
  have hi := (integrable_periodise ρ hρ hε).mul_bdd
    (measurable_periodise ρ hρ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun v => by
      simpa only [Real.norm_eq_abs] using hB v)
  apply (memLp_two_iff_integrable_sq
    (measurable_periodise ρ hρ).aestronglyMeasurable).mpr
  simpa only [pow_two] using hi

theorem stochasticHeatKernel_time_difference_eq_bare_averaging
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {ε s : ℝ} (hε : 0 < ε) (hs : 0 < s) (z z' w : SpaceTime) :
    stochasticHeatKernel ρ ε s z w - stochasticHeatKernel ρ ε s z' w =
      ∫ v : SpaceTime,
        (bareHeatRegularisedKernel s (z - (w + v)) -
          bareHeatRegularisedKernel s (z' - (w + v))) * periodise ρ ε v := by
  have hm := memLp_bareHeatRegularisedKernel hs
  have hp2 := memLp_periodise_two_local ρ hρ hε
  have hi := (memLp_comp_sub_left_spaceTime hm (z - w)).integrable_mul hp2
  have hi' := (memLp_comp_sub_left_spaceTime hm (z' - w)).integrable_mul hp2
  rw [stochasticHeatKernel_eq_bare_convolution ρ hρ hε hs,
    stochasticHeatKernel_eq_bare_convolution ρ hρ hε hs,
    ← integral_sub
      (f := fun v => bareHeatRegularisedKernel s (z - w - v) * periodise ρ ε v)
      (g := fun v => bareHeatRegularisedKernel s (z' - w - v) * periodise ρ ε v) hi hi']
  apply integral_congr_ae
  filter_upwards [] with v
  rw [sub_mul]
  have hz : z - w - v = z - (w + v) := by abel
  have hz' : z' - w - v = z' - (w + v) := by abel
  rw [hz, hz']

theorem stochasticHeatKernel_time_increment_sq_bound_uniform
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε s : ℝ}, 0 < ε → ε ≤ 1 → 0 < s → s ≤ 1 →
      ∀ t t' : ℝ, ∀ x : Torus3,
      (∫ w : SpaceTime,
        (stochasticHeatKernel ρ ε s (t, x) w -
          stochasticHeatKernel ρ ε s (t', x) w) ^ 2) ≤
        C * |t - t'| ^ θ * s ^ (-(1 / 2 + θ : ℝ)) := by
  obtain ⟨C₀, hC₀, hbare⟩ :=
    integral_bareHeatRegularisedKernel_pair_time_increment_sq_bound hθ hθ1
  let N : ℝ := ∫ v : ℝ × (Fin 3 → ℝ), |ρ v|
  refine ⟨N ^ 2 * C₀, mul_nonneg (sq_nonneg _) hC₀, ?_⟩
  intro ε s hε hε1 hs hs1 t t' x
  let f : SpaceTime → ℝ := fun w =>
    bareHeatRegularisedKernel s ((t, x) - w) -
      bareHeatRegularisedKernel s ((t', x) - w)
  have hfm : Measurable f :=
    ((measurable_bareHeatRegularisedKernel s).comp (measurable_const.sub measurable_id)).sub
      ((measurable_bareHeatRegularisedKernel s).comp (measurable_const.sub measurable_id))
  have hm := memLp_bareHeatRegularisedKernel hs
  have hf2 : MemLp f 2 :=
    (memLp_comp_sub_left_spaceTime hm (t, x)).sub
      (memLp_comp_sub_left_spaceTime hm (t', x))
  obtain ⟨B, hB⟩ := bounded_periodise ρ hρ hε
  have hyoung := integral_add_averaging_sq_le_abs_mass_sq hfm hf2
    (measurable_periodise ρ hρ) (integrable_periodise ρ hρ hε) hB
  have hNε : (∫ v : SpaceTime, |periodise ρ ε v|) ≤ N := by
    exact (integral_abs_periodise_le ρ hρ hε hε1).trans_eq (integral_abs_rescale_eq ρ hε)
  have hNε0 : 0 ≤ ∫ v : SpaceTime, |periodise ρ ε v| :=
    integral_nonneg fun v => abs_nonneg _
  have hNsq : (∫ v : SpaceTime, |periodise ρ ε v|) ^ 2 ≤ N ^ 2 :=
    pow_le_pow_left₀ hNε0 hNε 2
  calc
    _ = ∫ w : SpaceTime, (∫ v : SpaceTime, f (w + v) * periodise ρ ε v) ^ 2 := by
      apply integral_congr_ae
      filter_upwards [] with w
      rw [stochasticHeatKernel_time_difference_eq_bare_averaging ρ hρ hε hs]
    _ ≤ (∫ v : SpaceTime, |periodise ρ ε v|) ^ 2 * ∫ w : SpaceTime, f w ^ 2 := hyoung
    _ ≤ N ^ 2 * ∫ w : SpaceTime, f w ^ 2 :=
      mul_le_mul_of_nonneg_right hNsq (integral_nonneg fun w => sq_nonneg _)
    _ ≤ N ^ 2 * (C₀ * |t - t'| ^ θ * s ^ (-(1 / 2 + θ : ℝ))) :=
      mul_le_mul_of_nonneg_left (hbare hs hs1 t t' x) (sq_nonneg _)
    _ = (N ^ 2 * C₀) * |t - t'| ^ θ * s ^ (-(1 / 2 + θ : ℝ)) := by ring

end RegularityStructures.Phi43

end
