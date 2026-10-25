/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergenceBareSymmetry
public import Phi43.Stochastic.StochasticHeatConvergenceResolventTime

/-!
# The iterated bare covariance as a massive-kernel resolvent

The spatial semigroup identity and the substitution `u = 2*s + |t| + 2*r`
reduce the positive-time iterated covariance to the resolvent estimated in the preceding
modules. The time-increment estimate here is unconditional and uniform in the spatial point.
-/

@[expose] public noncomputable section

open MeasureTheory Real Set

namespace RegularityStructures.Phi43

private theorem integral_time_tail_add (f : ℝ → ℝ) (a : ℝ) :
    ∫ r : ℝ in Ioi 0, f (a + r) = ∫ u : ℝ in Ioi a, f u := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  calc
    ∫ r : ℝ, (Ioi 0).indicator (fun r => f (a + r)) r =
        ∫ r : ℝ, (Ioi a).indicator f (a + r) := by
      apply integral_congr_ae
      filter_upwards [] with r
      simp only [indicator_apply, mem_Ioi, lt_add_iff_pos_right]
    _ = ∫ u : ℝ, (Ioi a).indicator f u := integral_add_left_eq_self _ a

theorem integral_massiveHeatKernel_affine_time_tail (a : ℝ) (x : Torus3) :
    ∫ r : ℝ in Ioi 0, massiveHeatKernel (a + 2 * r, x) =
      (1 / 2 : ℝ) * ∫ u : ℝ in Ioi a, massiveHeatKernel (u, x) := by
  have hscale := integral_comp_mul_left_Ioi
    (fun u : ℝ => massiveHeatKernel (a + u, x)) 0 (by norm_num : (0 : ℝ) < 2)
  simp only [mul_zero, smul_eq_mul] at hscale
  rw [integral_time_tail_add (fun u => massiveHeatKernel (u, x)) a] at hscale
  simpa only [one_div] using hscale

theorem integrableOn_massiveHeatKernel_affine_time_tail
    {a : ℝ} (ha : 0 < a) (x : Torus3) :
    IntegrableOn (fun r : ℝ => massiveHeatKernel (a + 2 * r, x)) (Ioi 0) := by
  have hi := (integrableOn_massiveHeatKernel_time_tail ha x).integrable_indicator
    measurableSet_Ioi
  have hj := (measurePreserving_add_left (volume : Measure ℝ) a).integrable_comp_of_integrable hi
  have hadd : IntegrableOn (fun r : ℝ => massiveHeatKernel (a + r, x)) (Ioi 0) := by
    rw [← integrable_indicator_iff measurableSet_Ioi]
    convert hj using 1
    funext r
    simp only [Function.comp_def, indicator_apply, mem_Ioi, lt_add_iff_pos_right]
  apply (integrableOn_Ioi_comp_mul_left_iff
    (fun u : ℝ => massiveHeatKernel (a + u, x)) 0 (by norm_num : (0 : ℝ) < 2)).mpr
  simpa only [mul_zero] using hadd

theorem integral_heatRegularised_massive_spatial_covariance
    {s r : ℝ} (hs : 0 < s) (hr : 0 < r) (t : ℝ) (x : Torus3) :
    ∫ y : Torus3,
        (exp (-(|t| + r)) * heatKernel (s + |t| + r) (x + y)) *
          (exp (-r) * heatKernel (s + r) y) =
      exp (-(|t| + 2 * r)) * heatKernel (2 * s + |t| + 2 * r) x := by
  have hsr : 0 < s + r := add_pos hs hr
  have hstr : 0 < s + |t| + r := by linarith only [hs, hr, abs_nonneg t]
  calc
    _ = (exp (-(|t| + r)) * exp (-r)) *
        ∫ y : Torus3, heatKernel (s + r) y * heatKernel (s + |t| + r) (x + y) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      ring
    _ = exp (-(|t| + 2 * r)) * heatKernel (2 * s + |t| + 2 * r) x := by
      rw [integral_heatKernel_mul_heatKernel_add hsr hstr x, ← exp_add]
      congr 2 <;> ring

theorem integral_heatRegularised_massive_spatial_covariance_eq_shift
    {s r : ℝ} (hs : 0 < s) (hr : 0 < r) (t : ℝ) (x : Torus3) :
    (∫ y : Torus3,
        (exp (-(|t| + r)) * heatKernel (s + |t| + r) (x + y)) *
          (exp (-r) * heatKernel (s + r) y)) =
      exp (2 * s) * massiveHeatKernel (2 * s + |t| + 2 * r, x) := by
  rw [integral_heatRegularised_massive_spatial_covariance hs hr t x]
  have htime : 0 < 2 * s + |t| + 2 * r := by
    linarith only [hs, hr, abs_nonneg t]
  simp only [massiveHeatKernel, htime, ite_true]
  rw [← mul_assoc, ← exp_add]
  congr 2
  ring

theorem integrableOn_heatRegularised_massive_covariance
    {s : ℝ} (hs : 0 < s) (t : ℝ) (x : Torus3) :
    IntegrableOn (fun r : ℝ => ∫ y : Torus3,
      (exp (-(|t| + r)) * heatKernel (s + |t| + r) (x + y)) *
        (exp (-r) * heatKernel (s + r) y)) (Ioi 0) := by
  have ha : 0 < 2 * s + |t| := by linarith only [hs, abs_nonneg t]
  have hi := (integrableOn_massiveHeatKernel_affine_time_tail ha x).const_mul (exp (2 * s))
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  exact (integral_heatRegularised_massive_spatial_covariance_eq_shift hs hr t x).symm

theorem integrable_heatRegularised_massive_covariance_product
    {s : ℝ} (hs : 0 < s) (t : ℝ) (x : Torus3) :
    Integrable (fun p : ℝ × Torus3 =>
      (exp (-(|t| + p.1)) * heatKernel (s + |t| + p.1) (x + p.2)) *
        (exp (-p.1) * heatKernel (s + p.1) p.2))
      (((volume : Measure ℝ).restrict (Ioi 0)).prod (volume : Measure Torus3)) := by
  have hk1 : Measurable (fun p : ℝ × Torus3 =>
      heatKernel (s + |t| + p.1) (x + p.2)) :=
    measurable_heatKernel.comp
      ((measurable_const.add measurable_fst).prodMk
        (measurable_const.add measurable_snd))
  have hk2 : Measurable (fun p : ℝ × Torus3 => heatKernel (s + p.1) p.2) :=
    measurable_heatKernel.comp ((measurable_const.add measurable_fst).prodMk measurable_snd)
  have hm : Measurable (fun p : ℝ × Torus3 =>
      (exp (-(|t| + p.1)) * heatKernel (s + |t| + p.1) (x + p.2)) *
        (exp (-p.1) * heatKernel (s + p.1) p.2)) :=
    ((measurable_const.add measurable_fst).neg.exp.mul hk1).mul
      (measurable_fst.neg.exp.mul hk2)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := hr
    have hstr : 0 < s + |t| + r := by linarith only [hs, hr0, abs_nonneg t]
    have hsr : 0 < s + r := add_pos hs hr0
    have hc : Continuous (fun y : Torus3 =>
        (exp (-(|t| + r)) * heatKernel (s + |t| + r) (x + y)) *
          (exp (-r) * heatKernel (s + r) y)) :=
      (continuous_const.mul ((continuous_heatKernel_fixed hstr).comp
        (continuous_const.add continuous_id))).mul
          (continuous_const.mul (continuous_heatKernel_fixed hsr))
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · apply (integrableOn_heatRegularised_massive_covariance hs t x).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := hr
    have hstr : 0 < s + |t| + r := by linarith only [hs, hr0, abs_nonneg t]
    apply integral_congr_ae
    filter_upwards [] with y
    exact (Real.norm_of_nonneg
      (mul_nonneg (mul_nonneg (exp_nonneg _) (heatKernel_nonneg hstr _))
        (mul_nonneg (exp_nonneg _) (heatKernel_nonneg (add_pos hs hr0) _)))).symm

theorem integral_heatRegularised_massive_covariance_eq_resolvent
    {s : ℝ} (hs : 0 < s) (t : ℝ) (x : Torus3) :
    (∫ r : ℝ in Ioi 0, ∫ y : Torus3,
        (exp (-(|t| + r)) * heatKernel (s + |t| + r) (x + y)) *
          (exp (-r) * heatKernel (s + r) y)) =
      exp (2 * s) / 2 *
        ∫ u : ℝ in Ioi (2 * s + |t|), massiveHeatKernel (u, x) := by
  calc
    _ = ∫ r : ℝ in Ioi 0,
        exp (2 * s) * massiveHeatKernel (2 * s + |t| + 2 * r, x) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact integral_heatRegularised_massive_spatial_covariance_eq_shift hs hr t x
    _ = exp (2 * s) / 2 *
        ∫ u : ℝ in Ioi (2 * s + |t|), massiveHeatKernel (u, x) := by
      rw [integral_const_mul, integral_massiveHeatKernel_affine_time_tail]
      ring

end RegularityStructures.Phi43

end
