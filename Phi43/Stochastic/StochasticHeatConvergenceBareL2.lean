/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergenceBareKernel
public import Phi43.Stochastic.WhiteNoiseL2
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Square integrability and time increments of the bare smoothed kernel

The variance of a time difference is twice the loss in covariance. The resolvent time modulus
therefore gives the uniform L² estimate with the exponent of the time-increment bound before
mollification. Translations preserve the square integrability used in the algebraic expansion.
-/

@[expose] public noncomputable section

open MeasureTheory Real

namespace RegularityStructures.Phi43

theorem memLp_bareHeatRegularisedKernel {s : ℝ} (hs : 0 < s) :
    MemLp (bareHeatRegularisedKernel s) 2 := by
  have hi := integrable_bareHeatRegularisedKernel_covariance hs (t := 0) le_rfl 0
  change Integrable (fun w : SpaceTime =>
    bareHeatRegularisedKernel s (0 + w) * bareHeatRegularisedKernel s w) at hi
  apply (memLp_two_iff_integrable_sq
    (measurable_bareHeatRegularisedKernel s).aestronglyMeasurable).mpr
  simpa only [zero_add, pow_two] using hi

theorem integral_bareHeatRegularisedKernel_time_increment_sq
    {s h : ℝ} (hs : 0 < s) (hh : 0 ≤ h) :
    (∫ w : SpaceTime,
      (bareHeatRegularisedKernel s ((h, 0) + w) - bareHeatRegularisedKernel s w) ^ 2) =
      2 * ((∫ w : SpaceTime, bareHeatRegularisedKernel s w ^ 2) -
        ∫ w : SpaceTime, bareHeatRegularisedKernel s ((h, 0) + w) *
          bareHeatRegularisedKernel s w) := by
  have hm := memLp_bareHeatRegularisedKernel hs
  have hmshift := hm.comp_measurePreserving
    (measurePreserving_add_left (volume : Measure SpaceTime) (h, 0))
  have hi := hm.integrable_sq
  have hishift := hmshift.integrable_sq
  change Integrable (fun w : SpaceTime => bareHeatRegularisedKernel s ((h, 0) + w) ^ 2)
    at hishift
  have hcross := integrable_bareHeatRegularisedKernel_covariance hs hh 0
  calc
    _ = ∫ w : SpaceTime,
        (bareHeatRegularisedKernel s ((h, 0) + w) ^ 2 +
          bareHeatRegularisedKernel s w ^ 2) -
            2 * (bareHeatRegularisedKernel s ((h, 0) + w) *
              bareHeatRegularisedKernel s w) := by
      apply integral_congr_ae
      filter_upwards [] with w
      ring
    _ = ((∫ w : SpaceTime, bareHeatRegularisedKernel s ((h, 0) + w) ^ 2) +
          ∫ w : SpaceTime, bareHeatRegularisedKernel s w ^ 2) -
            2 * ∫ w : SpaceTime, bareHeatRegularisedKernel s ((h, 0) + w) *
              bareHeatRegularisedKernel s w := by
      rw [integral_sub
        (f := fun w : SpaceTime => bareHeatRegularisedKernel s ((h, 0) + w) ^ 2 +
          bareHeatRegularisedKernel s w ^ 2)
        (hishift.add hi) (hcross.const_mul 2),
        integral_add hishift hi, integral_const_mul]
    _ = 2 * ((∫ w : SpaceTime, bareHeatRegularisedKernel s w ^ 2) -
        ∫ w : SpaceTime, bareHeatRegularisedKernel s ((h, 0) + w) *
          bareHeatRegularisedKernel s w) := by
      rw [integral_comp_add_left_spaceTime (fun w => bareHeatRegularisedKernel s w ^ 2)]
      ring

theorem integral_bareHeatRegularisedKernel_time_increment_sq_bound
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {s h : ℝ}, 0 < s → s ≤ 1 → 0 ≤ h →
      (∫ w : SpaceTime,
        (bareHeatRegularisedKernel s ((h, 0) + w) - bareHeatRegularisedKernel s w) ^ 2) ≤
        C * h ^ θ * s ^ (-(1 / 2 + θ : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := heat_covariance_resolvent_time_increment_bound hθ hθ1
  refine ⟨2 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro s h hs hs1 hh
  have hzero : (∫ w : SpaceTime, bareHeatRegularisedKernel s w ^ 2) =
      exp (2 * s) / 2 *
        ∫ u : ℝ in Set.Ioi (2 * s + |(0 : ℝ)|), massiveHeatKernel (u, 0) := by
    have h := integral_bareHeatRegularisedKernel_covariance_eq_resolvent hs (t := 0) le_rfl 0
    change (∫ w : SpaceTime, bareHeatRegularisedKernel s (0 + w) *
      bareHeatRegularisedKernel s w) = _ at h
    simpa only [zero_add, pow_two] using h
  rw [integral_bareHeatRegularisedKernel_time_increment_sq hs hh, hzero,
    integral_bareHeatRegularisedKernel_covariance_eq_resolvent hs hh 0]
  have hmod := hbound hs hs1 0 h 0
  have htime : |(0 : ℝ) - h| = h := by
    rw [zero_sub, abs_neg, abs_of_nonneg hh]
  rw [htime] at hmod
  calc
    _ ≤ 2 * |(exp (2 * s) / 2 *
          ∫ u : ℝ in Set.Ioi (2 * s + |(0 : ℝ)|), massiveHeatKernel (u, 0)) -
        (exp (2 * s) / 2 *
          ∫ u : ℝ in Set.Ioi (2 * s + |h|), massiveHeatKernel (u, 0))| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)
    _ ≤ 2 * (C * h ^ θ * s ^ (-(1 / 2 + θ : ℝ))) :=
      mul_le_mul_of_nonneg_left hmod (by norm_num)
    _ = (2 * C) * h ^ θ * s ^ (-(1 / 2 + θ : ℝ)) := by ring

theorem integral_bareHeatRegularisedKernel_time_increment_sq_bound_abs
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {s : ℝ}, 0 < s → s ≤ 1 → ∀ h : ℝ,
      (∫ w : SpaceTime,
        (bareHeatRegularisedKernel s ((h, 0) + w) - bareHeatRegularisedKernel s w) ^ 2) ≤
        C * |h| ^ θ * s ^ (-(1 / 2 + θ : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := integral_bareHeatRegularisedKernel_time_increment_sq_bound hθ hθ1
  refine ⟨C, hC, ?_⟩
  intro s hs hs1 h
  by_cases hh : 0 ≤ h
  · simpa only [abs_of_nonneg hh] using hbound hs hs1 hh
  · have hneg : 0 ≤ -h := neg_nonneg.mpr (le_of_not_ge hh)
    have hcancel : (h, (0 : Torus3)) + (-h, 0) = (0 : SpaceTime) := by
      ext <;> simp
    have heq :
        (∫ w : SpaceTime,
          (bareHeatRegularisedKernel s ((h, 0) + w) - bareHeatRegularisedKernel s w) ^ 2) =
        ∫ w : SpaceTime,
          (bareHeatRegularisedKernel s ((-h, 0) + w) - bareHeatRegularisedKernel s w) ^ 2 := by
      calc
        _ = ∫ w : SpaceTime,
            (bareHeatRegularisedKernel s ((h, 0) + ((-h, 0) + w)) -
              bareHeatRegularisedKernel s ((-h, 0) + w)) ^ 2 :=
          (integral_comp_add_left_spaceTime
            (fun w => (bareHeatRegularisedKernel s ((h, 0) + w) -
              bareHeatRegularisedKernel s w) ^ 2) (-h, 0)).symm
        _ = _ := by
          apply integral_congr_ae
          filter_upwards [] with w
          rw [← add_assoc, hcancel, zero_add]
          ring
    rw [heq]
    simpa only [abs_of_nonpos (le_of_not_ge hh)] using hbound hs hs1 hneg

theorem integral_bareHeatRegularisedKernel_pair_time_increment_sq_bound
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {s : ℝ}, 0 < s → s ≤ 1 →
      ∀ t t' : ℝ, ∀ x : Torus3,
      (∫ w : SpaceTime,
        (bareHeatRegularisedKernel s ((t, x) - w) -
          bareHeatRegularisedKernel s ((t', x) - w)) ^ 2) ≤
        C * |t - t'| ^ θ * s ^ (-(1 / 2 + θ : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := integral_bareHeatRegularisedKernel_time_increment_sq_bound_abs hθ hθ1
  refine ⟨C, hC, ?_⟩
  intro s hs hs1 t t' x
  have heq := integral_comp_sub_left_spaceTime
    (fun w => (bareHeatRegularisedKernel s ((t, x) - w) -
      bareHeatRegularisedKernel s ((t', x) - w)) ^ 2) (t', x)
  have hfirst (w : SpaceTime) :
      (t, x) - ((t', x) - w) = (t - t', (0 : Torus3)) + w := by
    ext <;> simp
    abel
  have hsecond (w : SpaceTime) : (t', x) - ((t', x) - w) = w := sub_sub_cancel _ _
  simp only [hfirst, hsecond] at heq
  rw [← heq]
  exact hbound hs hs1 (t - t')

end RegularityStructures.Phi43

end
