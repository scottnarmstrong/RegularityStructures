/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergenceResolventBounds

/-!
# The time modulus of the spatially regularised covariance resolvent

The bare covariance after spatial heat regularisation is represented by
`exp (2*s) / 2` times the massive-kernel time tail starting at `2*s + |t|`.
This module estimates that explicit time-tail expression. Its identification with the
space-time convolution and averaging against mollifiers are separate steps.
-/

@[expose] public noncomputable section

open MeasureTheory Real Set

namespace RegularityStructures.Phi43

theorem massiveHeatKernel_shifted_time_tail_fractional_bound
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {s : ℝ}, 0 < s → ∀ t t' : ℝ, ∀ x : Torus3,
      |(∫ r : ℝ in Ioi (2 * s + |t|), massiveHeatKernel (r, x)) -
          ∫ r : ℝ in Ioi (2 * s + |t'|), massiveHeatKernel (r, x)| ≤
        C * |t - t'| ^ θ * s ^ (-(1 / 2 + θ : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := massiveHeatKernel_time_tail_fractional_increment_bound hθ hθ1
  refine ⟨C, hC, ?_⟩
  intro s hs t t' x
  wlog htt' : |t| ≤ |t'| generalizing t t'
  · have h := this t' t (le_of_not_ge htt')
    simpa only [abs_sub_comm] using h
  have ha : 0 < 2 * s + |t| := by linarith only [hs, abs_nonneg t]
  have hab : 2 * s + |t| ≤ 2 * s + |t'| := add_le_add le_rfl htt'
  have hdiff : 2 * s + |t'| - (2 * s + |t|) ≤ |t - t'| := by
    have h := abs_sub_abs_le_abs_sub t' t
    calc
      2 * s + |t'| - (2 * s + |t|) = |t'| - |t| := by ring
      _ ≤ |t' - t| := h
      _ = |t - t'| := abs_sub_comm _ _
  have hpowdiff : (2 * s + |t'| - (2 * s + |t|)) ^ θ ≤ |t - t'| ^ θ :=
    rpow_le_rpow (sub_nonneg.mpr hab) hdiff hθ
  have hbase : s ≤ 2 * s + |t| := by linarith only [hs, abs_nonneg t]
  have hneg : -(1 / 2 + θ : ℝ) ≤ 0 := by linarith only [hθ]
  have hpowbase := rpow_le_rpow_of_nonpos hs hbase hneg
  exact (hbound ha hab x).trans
    (mul_le_mul
      (mul_le_mul_of_nonneg_left hpowdiff hC) hpowbase
      (rpow_nonneg ha.le _) (mul_nonneg hC (rpow_nonneg (abs_nonneg _) _)))

theorem heat_covariance_resolvent_time_increment_bound
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {s : ℝ}, 0 < s → s ≤ 1 →
      ∀ t t' : ℝ, ∀ x : Torus3,
      |(exp (2 * s) / 2 *
          ∫ r : ℝ in Ioi (2 * s + |t|), massiveHeatKernel (r, x)) -
        (exp (2 * s) / 2 *
          ∫ r : ℝ in Ioi (2 * s + |t'|), massiveHeatKernel (r, x))| ≤
        C * |t - t'| ^ θ * s ^ (-(1 / 2 + θ : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := massiveHeatKernel_shifted_time_tail_fractional_bound hθ hθ1
  refine ⟨exp 2 / 2 * C, mul_nonneg (div_nonneg (exp_nonneg _) (by norm_num)) hC, ?_⟩
  intro s hs hs1 t t' x
  have hfactor : 0 ≤ exp (2 * s) / 2 := div_nonneg (exp_nonneg _) (by norm_num)
  have hexp : exp (2 * s) / 2 ≤ exp 2 / 2 := by
    exact div_le_div_of_nonneg_right
      (exp_le_exp.mpr (by linarith only [hs1])) (by norm_num)
  rw [← mul_sub, abs_mul, abs_of_nonneg hfactor]
  calc
    _ ≤ (exp (2 * s) / 2) *
        (C * |t - t'| ^ θ * s ^ (-(1 / 2 + θ : ℝ))) :=
      mul_le_mul_of_nonneg_left (hbound hs t t' x) hfactor
    _ ≤ (exp 2 / 2) * (C * |t - t'| ^ θ * s ^ (-(1 / 2 + θ : ℝ))) :=
      mul_le_mul_of_nonneg_right hexp
        (mul_nonneg (mul_nonneg hC (rpow_nonneg (abs_nonneg _) _))
          (rpow_nonneg hs.le _))
    _ = (exp 2 / 2 * C) * |t - t'| ^ θ * s ^ (-(1 / 2 + θ : ℝ)) := by ring

end RegularityStructures.Phi43

end
