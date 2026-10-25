/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergenceSpatialResolvent
public import Phi43.Stochastic.StochasticHeatConvergenceUniformSize

/-!
# Spatial L² increments of the bare spatially smoothed kernel

The spatial covariance modulus and nonnegativity give two bounds for the square of a
translation difference. Their interpolation supplies a positive spatial power for the
full space-time displacement estimate used in the space-time increment bound.
-/

@[expose] public noncomputable section

open MeasureTheory Real Set

namespace RegularityStructures.Phi43

theorem integral_bareHeatRegularisedKernel_spatial_increment_sq
    {s : ℝ} (hs : 0 < s) (x : Torus3) :
    (∫ w : SpaceTime,
      (bareHeatRegularisedKernel s ((0, x) + w) - bareHeatRegularisedKernel s w) ^ 2) =
      2 * ((∫ w : SpaceTime, bareHeatRegularisedKernel s w ^ 2) -
        ∫ w : SpaceTime, bareHeatRegularisedKernel s ((0, x) + w) *
          bareHeatRegularisedKernel s w) := by
  have hm := memLp_bareHeatRegularisedKernel hs
  have hmshift := hm.comp_measurePreserving
    (measurePreserving_add_left (volume : Measure SpaceTime) (0, x))
  have hi := hm.integrable_sq
  have hishift := hmshift.integrable_sq
  change Integrable (fun w : SpaceTime => bareHeatRegularisedKernel s ((0, x) + w) ^ 2)
    at hishift
  have hcross := integrable_bareHeatRegularisedKernel_covariance hs (t := 0) le_rfl x
  calc
    _ = ∫ w : SpaceTime,
        (bareHeatRegularisedKernel s ((0, x) + w) ^ 2 + bareHeatRegularisedKernel s w ^ 2) -
          2 * (bareHeatRegularisedKernel s ((0, x) + w) * bareHeatRegularisedKernel s w) := by
      apply integral_congr_ae
      filter_upwards [] with w
      ring
    _ = ((∫ w : SpaceTime, bareHeatRegularisedKernel s ((0, x) + w) ^ 2) +
          ∫ w : SpaceTime, bareHeatRegularisedKernel s w ^ 2) -
            2 * ∫ w : SpaceTime, bareHeatRegularisedKernel s ((0, x) + w) *
              bareHeatRegularisedKernel s w := by
      rw [integral_sub
        (f := fun w : SpaceTime => bareHeatRegularisedKernel s ((0, x) + w) ^ 2 +
          bareHeatRegularisedKernel s w ^ 2)
        (hishift.add hi) (hcross.const_mul 2),
        integral_add hishift hi, integral_const_mul]
    _ = _ := by
      rw [integral_comp_add_left_spaceTime (fun w => bareHeatRegularisedKernel s w ^ 2)]
      ring

theorem integral_bareHeatRegularisedKernel_spatial_increment_sq_le_size
    {s : ℝ} (hs : 0 < s) (x : Torus3) :
    (∫ w : SpaceTime,
      (bareHeatRegularisedKernel s ((0, x) + w) - bareHeatRegularisedKernel s w) ^ 2) ≤
      2 * ∫ w : SpaceTime, bareHeatRegularisedKernel s w ^ 2 := by
  rw [integral_bareHeatRegularisedKernel_spatial_increment_sq hs x]
  have hcross : 0 ≤ ∫ w : SpaceTime, bareHeatRegularisedKernel s ((0, x) + w) *
      bareHeatRegularisedKernel s w := integral_nonneg fun w =>
    mul_nonneg (bareHeatRegularisedKernel_nonneg hs _) (bareHeatRegularisedKernel_nonneg hs _)
  exact mul_le_mul_of_nonneg_left (sub_le_self _ hcross) (by norm_num)

theorem integral_bareHeatRegularisedKernel_spatial_increment_sq_linear_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {s : ℝ}, 0 < s → s ≤ 1 → ∀ x : Torus3,
      (∫ w : SpaceTime,
        (bareHeatRegularisedKernel s ((0, x) + w) - bareHeatRegularisedKernel s w) ^ 2) ≤
        C * torusSpatialNorm x * s ^ (-(1 : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := massiveHeatKernel_time_tail_spatial_modulus
  refine ⟨2 * exp 2 * C, mul_nonneg (mul_nonneg (by norm_num) (exp_nonneg _)) hC, ?_⟩
  intro s hs hs1 x
  have h2s : 0 < 2 * s := mul_pos (by norm_num) hs
  have hzero : (∫ w : SpaceTime, bareHeatRegularisedKernel s w ^ 2) =
      exp (2 * s) / 2 * ∫ u : ℝ in Ioi (2 * s), massiveHeatKernel (u, 0) := by
    have h := integral_bareHeatRegularisedKernel_covariance_eq_resolvent hs (t := 0) le_rfl 0
    change (∫ w : SpaceTime, bareHeatRegularisedKernel s (0 + w) *
      bareHeatRegularisedKernel s w) = _ at h
    simpa only [zero_add, pow_two, abs_zero, add_zero] using h
  have hinv : (2 * s)⁻¹ + 1 ≤ 2 * s⁻¹ := by
    have h1 : (2 * s)⁻¹ ≤ s⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hs (by linarith only [hs] : s ≤ 2 * s)
    have h2 : 1 ≤ s⁻¹ := by
      simpa only [one_div, inv_one] using one_div_le_one_div_of_le hs hs1
    calc
      _ ≤ s⁻¹ + s⁻¹ := add_le_add h1 h2
      _ = 2 * s⁻¹ := by ring
  have hexp : exp (2 * s) ≤ exp 2 := exp_le_exp.mpr (by linarith only [hs1])
  rw [integral_bareHeatRegularisedKernel_spatial_increment_sq hs x, hzero,
    integral_bareHeatRegularisedKernel_covariance_eq_resolvent hs (t := 0) le_rfl x]
  simp only [abs_zero, add_zero]
  calc
    _ = exp (2 * s) * ((∫ u : ℝ in Ioi (2 * s), massiveHeatKernel (u, 0)) -
        ∫ u : ℝ in Ioi (2 * s), massiveHeatKernel (u, x)) := by ring
    _ ≤ exp (2 * s) * |(∫ u : ℝ in Ioi (2 * s), massiveHeatKernel (u, x)) -
        ∫ u : ℝ in Ioi (2 * s), massiveHeatKernel (u, 0)| := by
      rw [abs_sub_comm]
      exact mul_le_mul_of_nonneg_left (le_abs_self _) (exp_nonneg _)
    _ ≤ exp 2 * (C * ((2 * s)⁻¹ + 1) * torusSpatialNorm x) :=
      mul_le_mul hexp (hbound h2s x) (abs_nonneg _) (exp_nonneg _)
    _ ≤ exp 2 * (C * (2 * s⁻¹) * torusSpatialNorm x) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinv hC)
          (torusSpatialNorm_nonneg _)) (exp_nonneg _)
    _ = (2 * exp 2 * C) * torusSpatialNorm x * s ^ (-(1 : ℝ)) := by
      rw [rpow_neg_one]
      ring

theorem integral_bareHeatRegularisedKernel_spatial_increment_sq_fractional_bound
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {s : ℝ}, 0 < s → s ≤ 1 → ∀ x : Torus3,
      (∫ w : SpaceTime,
        (bareHeatRegularisedKernel s ((0, x) + w) - bareHeatRegularisedKernel s w) ^ 2) ≤
        C * torusSpatialNorm x ^ θ * s ^ (-(1 / 2 + θ / 2 : ℝ)) := by
  obtain ⟨A₀, hA₀, hsize⟩ := integral_bareHeatRegularisedKernel_sq_bound_uniform
  obtain ⟨B, hB, hlinear⟩ := integral_bareHeatRegularisedKernel_spatial_increment_sq_linear_bound
  let A : ℝ := 2 * A₀
  have hA : 0 ≤ A := mul_nonneg (by norm_num) hA₀
  refine ⟨A ^ (1 - θ) * B ^ θ, mul_nonneg (rpow_nonneg hA _) (rpow_nonneg hB _), ?_⟩
  intro s hs hs1 x
  have hfirst : (∫ w : SpaceTime,
      (bareHeatRegularisedKernel s ((0, x) + w) - bareHeatRegularisedKernel s w) ^ 2) ≤
      A * s ^ (-(1 / 2 : ℝ)) := by
    exact (integral_bareHeatRegularisedKernel_spatial_increment_sq_le_size hs x).trans
      (by simpa only [A, mul_assoc] using mul_le_mul_of_nonneg_left (hsize hs hs1) (by norm_num : (0 : ℝ) ≤ 2))
  have hinterp := le_rpow_interpolation
    (integral_nonneg fun w : SpaceTime => sq_nonneg
      (bareHeatRegularisedKernel s ((0, x) + w) - bareHeatRegularisedKernel s w))
    (mul_nonneg hA (rpow_nonneg hs.le _))
    (mul_nonneg (mul_nonneg hB (torusSpatialNorm_nonneg x)) (rpow_nonneg hs.le _))
    hθ hθ1 hfirst (hlinear hs hs1 x)
  have hfactor : (A * s ^ (-(1 / 2 : ℝ))) ^ (1 - θ) *
      (B * torusSpatialNorm x * s ^ (-(1 : ℝ))) ^ θ =
        A ^ (1 - θ) * B ^ θ * torusSpatialNorm x ^ θ *
          s ^ (-(1 / 2 + θ / 2 : ℝ)) := by
    rw [mul_rpow hA (rpow_nonneg hs.le _),
      mul_rpow (mul_nonneg hB (torusSpatialNorm_nonneg _)) (rpow_nonneg hs.le _),
      mul_rpow hB (torusSpatialNorm_nonneg _), ← rpow_mul hs.le, ← rpow_mul hs.le]
    have hcombine : s ^ (-(1 / 2 : ℝ) * (1 - θ)) * s ^ (-(1 : ℝ) * θ) =
        s ^ (-(1 / 2 + θ / 2 : ℝ)) := by
      rw [← rpow_add hs]
      congr 1
      ring
    calc
      _ = A ^ (1 - θ) * B ^ θ * torusSpatialNorm x ^ θ *
          (s ^ (-(1 / 2 : ℝ) * (1 - θ)) * s ^ (-(1 : ℝ) * θ)) := by ring
      _ = _ := by rw [hcombine]
  rw [hfactor] at hinterp
  exact hinterp

end RegularityStructures.Phi43

end
