/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergenceSpatialBareL2

/-!
# Full parabolic displacement modulus of the bare kernel in L²

The time modulus at exponent `θ/2` and spatial modulus at exponent `θ` have the same
heat-scale singularity. Splitting a general translation into its two components yields
the parabolic displacement estimate averaged against the zero-mass mollifier difference.
-/

@[expose] public noncomputable section

open MeasureTheory Real

namespace RegularityStructures.Phi43

private theorem square_sub_le_twice_squares (a b c : ℝ) :
    (a - b) ^ 2 ≤ 2 * (a - c) ^ 2 + 2 * (c - b) ^ 2 := by
  nlinarith only [sq_nonneg (a - 2 * c + b)]

theorem bareHeatRegularisedKernel_displacement_sq_bound
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {s : ℝ}, 0 < s → s ≤ 1 → ∀ v : SpaceTime,
      (∫ w : SpaceTime, (bareHeatRegularisedKernel s (v + w) -
        bareHeatRegularisedKernel s w) ^ 2) ≤
        C * torusParabolicSize v ^ θ * s ^ (-(1 / 2 + θ / 2 : ℝ)) := by
  have hhalf : 0 ≤ θ / 2 := div_nonneg hθ (by norm_num)
  have hhalf1 : θ / 2 ≤ 1 := by linarith only [hθ1]
  obtain ⟨A, hA, htime⟩ := integral_bareHeatRegularisedKernel_time_increment_sq_bound_abs hhalf hhalf1
  obtain ⟨B, hB, hspace⟩ := integral_bareHeatRegularisedKernel_spatial_increment_sq_fractional_bound hθ hθ1
  refine ⟨2 * (A + B), mul_nonneg (by norm_num) (add_nonneg hA hB), ?_⟩
  intro s hs hs1 v
  have hm := memLp_bareHeatRegularisedKernel hs
  have hmv := hm.comp_measurePreserving
    (measurePreserving_add_left (volume : Measure SpaceTime) v)
  have hmx := hm.comp_measurePreserving
    (measurePreserving_add_left (volume : Measure SpaceTime) (0, v.2))
  have hF : Integrable (fun w : SpaceTime =>
      (bareHeatRegularisedKernel s (v + w) - bareHeatRegularisedKernel s w) ^ 2) :=
    (hmv.sub hm).integrable_sq
  have hT : Integrable (fun w : SpaceTime =>
      (bareHeatRegularisedKernel s (v + w) - bareHeatRegularisedKernel s ((0, v.2) + w)) ^ 2) :=
    (hmv.sub hmx).integrable_sq
  have hS : Integrable (fun w : SpaceTime =>
      (bareHeatRegularisedKernel s ((0, v.2) + w) - bareHeatRegularisedKernel s w) ^ 2) :=
    (hmx.sub hm).integrable_sq
  have htimeEq :
      (∫ w : SpaceTime, (bareHeatRegularisedKernel s (v + w) -
        bareHeatRegularisedKernel s ((0, v.2) + w)) ^ 2) =
      ∫ w : SpaceTime, (bareHeatRegularisedKernel s ((v.1, 0) + w) -
        bareHeatRegularisedKernel s w) ^ 2 := by
    have hpair : (v.1, (0 : Torus3)) + (0, v.2) = v := by ext <;> simp
    have harg (w : SpaceTime) : (v.1, (0 : Torus3)) + ((0, v.2) + w) = v + w := by
      rw [← add_assoc, hpair]
    calc
      _ = ∫ w : SpaceTime,
          (bareHeatRegularisedKernel s ((v.1, 0) + ((0, v.2) + w)) -
            bareHeatRegularisedKernel s ((0, v.2) + w)) ^ 2 := by
        apply integral_congr_ae
        filter_upwards [] with w
        rw [harg]
      _ = _ := integral_comp_add_left_spaceTime
        (fun w => (bareHeatRegularisedKernel s ((v.1, 0) + w) -
          bareHeatRegularisedKernel s w) ^ 2) (0, v.2)
  have htimepow : |v.1| ^ (θ / 2) ≤ torusParabolicSize v ^ θ := by
    have heq : (√|v.1|) ^ θ = |v.1| ^ (θ / 2) := by
      rw [sqrt_eq_rpow, ← rpow_mul (abs_nonneg _)]
      congr 1
      ring
    rw [← heq]
    exact rpow_le_rpow (sqrt_nonneg _)
      (le_add_of_nonneg_right (torusSpatialNorm_nonneg _)) hθ
  have hspacepow : torusSpatialNorm v.2 ^ θ ≤ torusParabolicSize v ^ θ :=
    rpow_le_rpow (torusSpatialNorm_nonneg _)
      (le_add_of_nonneg_left (sqrt_nonneg _)) hθ
  have hTb : (∫ w : SpaceTime, (bareHeatRegularisedKernel s (v + w) -
      bareHeatRegularisedKernel s ((0, v.2) + w)) ^ 2) ≤
      A * torusParabolicSize v ^ θ * s ^ (-(1 / 2 + θ / 2 : ℝ)) := by
    rw [htimeEq]
    exact (htime hs hs1 v.1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left htimepow hA) (rpow_nonneg hs.le _))
  have hSb := (hspace hs hs1 v.2).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hspacepow hB) (rpow_nonneg hs.le _))
  calc
    _ ≤ ∫ w : SpaceTime,
        2 * (bareHeatRegularisedKernel s (v + w) - bareHeatRegularisedKernel s ((0, v.2) + w)) ^ 2 +
          2 * (bareHeatRegularisedKernel s ((0, v.2) + w) - bareHeatRegularisedKernel s w) ^ 2 :=
      integral_mono hF ((hT.const_mul 2).add (hS.const_mul 2))
        (fun w => square_sub_le_twice_squares _ _ _)
    _ = 2 * (∫ w : SpaceTime, (bareHeatRegularisedKernel s (v + w) -
          bareHeatRegularisedKernel s ((0, v.2) + w)) ^ 2) +
        2 * ∫ w : SpaceTime, (bareHeatRegularisedKernel s ((0, v.2) + w) -
          bareHeatRegularisedKernel s w) ^ 2 := by
      rw [integral_add (f := fun w =>
        2 * (bareHeatRegularisedKernel s (v + w) - bareHeatRegularisedKernel s ((0, v.2) + w)) ^ 2)
        (hT.const_mul 2) (hS.const_mul 2), integral_const_mul, integral_const_mul]
    _ ≤ 2 * (A * torusParabolicSize v ^ θ * s ^ (-(1 / 2 + θ / 2 : ℝ))) +
        2 * (B * torusParabolicSize v ^ θ * s ^ (-(1 / 2 + θ / 2 : ℝ))) :=
      add_le_add (mul_le_mul_of_nonneg_left hTb (by norm_num))
        (mul_le_mul_of_nonneg_left hSb (by norm_num))
    _ = (2 * (A + B)) * torusParabolicSize v ^ θ * s ^ (-(1 / 2 + θ / 2 : ℝ)) := by ring

theorem bareHeatRegularisedKernel_centered_displacement_sq_bound
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {s : ℝ}, 0 < s → s ≤ 1 → ∀ z v : SpaceTime,
      (∫ w : SpaceTime, (bareHeatRegularisedKernel s (z - w - v) -
        bareHeatRegularisedKernel s (z - w)) ^ 2) ≤
        C * torusParabolicSize v ^ θ * s ^ (-(1 / 2 + θ / 2 : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := bareHeatRegularisedKernel_displacement_sq_bound hθ hθ1
  refine ⟨C, hC, ?_⟩
  intro s hs hs1 z v
  have hchange := integral_comp_sub_left_spaceTime
    (fun w => (bareHeatRegularisedKernel s (z - w - v) -
      bareHeatRegularisedKernel s (z - w)) ^ 2) (z - v)
  have hsecond (w : SpaceTime) : z - ((z - v) - w) = v + w := by abel
  have hthird (w : SpaceTime) : v + w - v = w := by abel
  simp only [hsecond, hthird] at hchange
  rw [← hchange]
  have heq : (∫ w : SpaceTime, (bareHeatRegularisedKernel s w -
      bareHeatRegularisedKernel s (v + w)) ^ 2) =
      ∫ w : SpaceTime, (bareHeatRegularisedKernel s (v + w) -
        bareHeatRegularisedKernel s w) ^ 2 := by
    apply integral_congr_ae
    filter_upwards [] with w
    ring
  rw [heq]
  exact hbound hs hs1 v

end RegularityStructures.Phi43

end
