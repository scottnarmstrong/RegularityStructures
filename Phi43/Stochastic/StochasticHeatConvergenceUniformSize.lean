/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergenceUniformTime
public import Phi43.Stochastic.StochasticHeatConvergenceMoments

/-!
# Uniform size bound for the heat-smoothed field without stochastic Fubini hypotheses

The resolvent size estimate controls the bare kernel in L². Signed mollifier averaging
preserves that estimate up to the square of the mollifier's L¹ norm. White-noise isometry
then proves the uniform annealed size bound for the canonical heat-smoothed field.
-/

@[expose] public noncomputable section

open MeasureTheory Real

namespace RegularityStructures.Phi43

theorem integral_bareHeatRegularisedKernel_sq_bound_uniform :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {s : ℝ}, 0 < s → s ≤ 1 →
      (∫ w : SpaceTime, bareHeatRegularisedKernel s w ^ 2) ≤ C * s ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := massiveHeatKernel_time_tail_bound
  refine ⟨exp 2 / 2 * C, mul_nonneg (div_nonneg (exp_nonneg _) (by norm_num)) hC, ?_⟩
  intro s hs hs1
  have h2s : 0 < 2 * s := mul_pos (by norm_num) hs
  have hzero : (∫ w : SpaceTime, bareHeatRegularisedKernel s w ^ 2) =
      exp (2 * s) / 2 * ∫ u : ℝ in Set.Ioi (2 * s), massiveHeatKernel (u, 0) := by
    have h := integral_bareHeatRegularisedKernel_covariance_eq_resolvent hs (t := 0) le_rfl 0
    change (∫ w : SpaceTime, bareHeatRegularisedKernel s (0 + w) *
      bareHeatRegularisedKernel s w) = _ at h
    simpa only [zero_add, pow_two, abs_zero, add_zero] using h
  have hexp : exp (2 * s) / 2 ≤ exp 2 / 2 :=
    div_le_div_of_nonneg_right (exp_le_exp.mpr (by linarith only [hs1])) (by norm_num)
  have hpow : (2 * s) ^ (-(1 / 2 : ℝ)) ≤ s ^ (-(1 / 2 : ℝ)) :=
    rpow_le_rpow_of_nonpos hs (by linarith only [hs]) (by norm_num)
  have htail := (hbound h2s (0 : Torus3)).trans (mul_le_mul_of_nonneg_left hpow hC)
  rw [hzero]
  calc
    _ ≤ (exp (2 * s) / 2) * |∫ u : ℝ in Set.Ioi (2 * s), massiveHeatKernel (u, 0)| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (div_nonneg (exp_nonneg _) (by norm_num))
    _ ≤ (exp 2 / 2) * (C * s ^ (-(1 / 2 : ℝ))) :=
      mul_le_mul hexp htail (abs_nonneg _) (div_nonneg (exp_nonneg _) (by norm_num))
    _ = (exp 2 / 2 * C) * s ^ (-(1 / 2 : ℝ)) := by ring

theorem stochasticHeatKernel_sq_le_abs_periodise_mass_sq
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {ε s : ℝ} (hε : 0 < ε) (hs : 0 < s) (z : SpaceTime) :
    (∫ w : SpaceTime, stochasticHeatKernel ρ ε s z w ^ 2) ≤
      (∫ v : SpaceTime, |periodise ρ ε v|) ^ 2 *
        ∫ w : SpaceTime, bareHeatRegularisedKernel s w ^ 2 := by
  let f : SpaceTime → ℝ := fun w => bareHeatRegularisedKernel s (z - w)
  have hf : Measurable f :=
    (measurable_bareHeatRegularisedKernel s).comp (measurable_const.sub measurable_id)
  have hf2 : MemLp f 2 := memLp_comp_sub_left_spaceTime (memLp_bareHeatRegularisedKernel hs) z
  obtain ⟨B, hB⟩ := bounded_periodise ρ hρ hε
  have hyoung := integral_add_averaging_sq_le_abs_mass_sq hf hf2
    (measurable_periodise ρ hρ) (integrable_periodise ρ hρ hε) hB
  have heq (w : SpaceTime) : stochasticHeatKernel ρ ε s z w =
      ∫ v : SpaceTime, f (w + v) * periodise ρ ε v := by
    rw [stochasticHeatKernel_eq_bare_convolution ρ hρ hε hs]
    apply integral_congr_ae
    filter_upwards [] with v
    have harg : z - w - v = z - (w + v) := by abel
    rw [harg]
  have hnorm : (∫ w : SpaceTime, f w ^ 2) =
      ∫ w : SpaceTime, bareHeatRegularisedKernel s w ^ 2 :=
    integral_comp_sub_left_spaceTime (fun w => bareHeatRegularisedKernel s w ^ 2) z
  simpa only [← heq, hnorm] using hyoung

theorem stochasticHeatKernel_sq_bound_uniform
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε s : ℝ}, 0 < ε → ε ≤ 1 → 0 < s → s ≤ 1 →
      ∀ z : SpaceTime, (∫ w : SpaceTime, stochasticHeatKernel ρ ε s z w ^ 2) ≤
        C * s ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨C₀, hC₀, hbare⟩ := integral_bareHeatRegularisedKernel_sq_bound_uniform
  let N : ℝ := ∫ v : ℝ × (Fin 3 → ℝ), |ρ v|
  refine ⟨N ^ 2 * C₀, mul_nonneg (sq_nonneg _) hC₀, ?_⟩
  intro ε s hε hε1 hs hs1 z
  have hNε : (∫ v : SpaceTime, |periodise ρ ε v|) ≤ N :=
    (integral_abs_periodise_le ρ hρ hε hε1).trans_eq (integral_abs_rescale_eq ρ hε)
  have hNsq := pow_le_pow_left₀
    (integral_nonneg fun v : SpaceTime => abs_nonneg (periodise ρ ε v)) hNε 2
  calc
    _ ≤ (∫ v : SpaceTime, |periodise ρ ε v|) ^ 2 *
        ∫ w : SpaceTime, bareHeatRegularisedKernel s w ^ 2 :=
      stochasticHeatKernel_sq_le_abs_periodise_mass_sq ρ hρ hε hs z
    _ ≤ N ^ 2 * ∫ w : SpaceTime, bareHeatRegularisedKernel s w ^ 2 :=
      mul_le_mul_of_nonneg_right hNsq (integral_nonneg fun w => sq_nonneg _)
    _ ≤ N ^ 2 * (C₀ * s ^ (-(1 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left (hbare hs hs1) (sq_nonneg _)
    _ = (N ^ 2 * C₀) * s ^ (-(1 / 2 : ℝ)) := by ring

end RegularityStructures.Phi43

end
