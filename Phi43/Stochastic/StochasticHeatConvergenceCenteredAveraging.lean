/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergenceYoungL2
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Averaging translation differences in L²

The weighted square inequality is integrated before discarding the displacement dependence. This
retains the cancellation needed for the space-time increment bound, unlike the ordinary Young
inequality.
-/

public noncomputable section

open MeasureTheory Real

namespace RegularityStructures.Phi43

private theorem square_sub_le_two (a b : ℝ) : (a - b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith only [sq_nonneg (a + b)]

private theorem integrable_add_translation_square_weight
    {f p : SpaceTime → ℝ} (hf : Measurable f) (hf2 : MemLp f 2)
    (hp : Measurable p) (hp1 : Integrable p) :
    Integrable (fun q : SpaceTime × SpaceTime => f (q.2 + q.1) ^ 2 * |p q.1|)
      ((volume : Measure SpaceTime).prod volume) := by
  have hm : Measurable (fun q : SpaceTime × SpaceTime => f (q.2 + q.1) ^ 2 * |p q.1|) :=
    ((hf.comp (measurable_snd.add measurable_fst)).pow_const 2).mul
      (hp.comp measurable_fst).norm
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [] with v
    exact ((measurePreserving_add_right (volume : Measure SpaceTime) v).integrable_comp_of_integrable
      hf2.integrable_sq).mul_const |p v|
  · apply (hp1.norm.const_mul (∫ w : SpaceTime, f w ^ 2)).congr
    filter_upwards [] with v
    symm
    calc
      _ = ∫ w : SpaceTime, f (w + v) ^ 2 * |p v| := by
        apply integral_congr_ae
        filter_upwards [] with w
        exact Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (abs_nonneg _))
      _ = (∫ w : SpaceTime, f w ^ 2) * |p v| := by
        rw [integral_mul_const, integral_add_right_eq_self (fun w => f w ^ 2) v]

theorem integrable_centered_add_translation_square_weight
    {f p : SpaceTime → ℝ} (hf : Measurable f) (hf2 : MemLp f 2)
    (hp : Measurable p) (hp1 : Integrable p) :
    Integrable (fun q : SpaceTime × SpaceTime => (f (q.2 + q.1) - f q.2) ^ 2 * |p q.1|)
      ((volume : Measure SpaceTime).prod volume) := by
  have hshift := integrable_add_translation_square_weight hf hf2 hp hp1
  have hbase := hp1.norm.mul_prod hf2.integrable_sq
  have hm : Measurable (fun q : SpaceTime × SpaceTime =>
      (f (q.2 + q.1) - f q.2) ^ 2 * |p q.1|) :=
    (((hf.comp (measurable_snd.add measurable_fst)).sub (hf.comp measurable_snd)).pow_const 2).mul
      (hp.comp measurable_fst).norm
  apply ((hshift.const_mul 2).add (hbase.const_mul 2)).mono' hm.aestronglyMeasurable
  filter_upwards [] with q
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (abs_nonneg _))]
  calc
    _ ≤ (2 * f (q.2 + q.1) ^ 2 + 2 * f q.2 ^ 2) * |p q.1| :=
      mul_le_mul_of_nonneg_right (square_sub_le_two _ _) (abs_nonneg _)
    _ = 2 * (f (q.2 + q.1) ^ 2 * |p q.1|) + 2 * (|p q.1| * f q.2 ^ 2) := by ring

theorem integral_centered_add_averaging_sq_le
    {f p : SpaceTime → ℝ} (hf : Measurable f) (hf2 : MemLp f 2)
    (hp : Measurable p) (hp1 : Integrable p) {B : ℝ} (hpB : ∀ v, |p v| ≤ B) :
    (∫ w : SpaceTime, (∫ v : SpaceTime, (f (w + v) - f w) * p v) ^ 2) ≤
      (∫ v : SpaceTime, |p v|) *
        ∫ v : SpaceTime, |p v| * ∫ w : SpaceTime, (f (w + v) - f w) ^ 2 := by
  have hp2 : MemLp p 2 := by
    apply (memLp_two_iff_integrable_sq hp.aestronglyMeasurable).mpr
    have hi := hp1.mul_bdd hp.aestronglyMeasurable
      (Filter.Eventually.of_forall fun v => by simpa only [Real.norm_eq_abs] using hpB v)
    simpa only [pow_two] using hi
  have hcenter := integrable_centered_add_translation_square_weight hf hf2 hp hp1
  have hpoint : ∀ᵐ w : SpaceTime,
      (∫ v : SpaceTime, (f (w + v) - f w) * p v) ^ 2 ≤
        (∫ v : SpaceTime, |p v|) * ∫ v : SpaceTime, (f (w + v) - f w) ^ 2 * |p v| := by
    filter_upwards [hcenter.prod_left_ae] with w hi
    have hfshift := hf2.comp_measurePreserving
      (measurePreserving_add_left (volume : Measure SpaceTime) w)
    have hfp : Integrable (fun v : SpaceTime => (f (w + v) - f w) * p v) := by
      apply ((hfshift.integrable_mul hp2).sub (hp1.const_mul (f w))).congr
      filter_upwards [] with v
      simp only [Pi.sub_apply, Function.comp_apply, Pi.mul_apply]
      ring
    exact integral_mul_sq_le_abs_mass hp1 hfp hi
  have hmajor : Integrable (fun w : SpaceTime => (∫ v : SpaceTime, |p v|) *
      ∫ v : SpaceTime, (f (w + v) - f w) ^ 2 * |p v|) :=
    hcenter.integral_prod_right.const_mul _
  have hconv : Measurable (fun w : SpaceTime =>
      ∫ v : SpaceTime, (f (w + v) - f w) * p v) :=
    (((hf.comp (measurable_fst.add measurable_snd)).sub (hf.comp measurable_fst)).mul
      (hp.comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable
  have hconv2 : Integrable (fun w : SpaceTime =>
      (∫ v : SpaceTime, (f (w + v) - f w) * p v) ^ 2) := by
    apply hmajor.mono' (hconv.pow_const 2).aestronglyMeasurable
    filter_upwards [hpoint] with w hw
    rwa [Real.norm_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ ∫ w : SpaceTime, (∫ v : SpaceTime, |p v|) *
        ∫ v : SpaceTime, (f (w + v) - f w) ^ 2 * |p v| :=
      integral_mono_ae hconv2 hmajor hpoint
    _ = (∫ v : SpaceTime, |p v|) *
        ∫ v : SpaceTime, ∫ w : SpaceTime, (f (w + v) - f w) ^ 2 * |p v| := by
      rw [integral_const_mul]
      congr 1
      exact integral_integral_swap
        (f := fun w v : SpaceTime => (f (w + v) - f w) ^ 2 * |p v|) hcenter.swap
    _ = _ := by
      simp_rw [integral_mul_const]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with v
      ring

end RegularityStructures.Phi43

end
