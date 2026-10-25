/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergenceWeightedSquare
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The L¹--L² averaging estimate on space-time

Translation invariance and the weighted square estimate give Young's inequality for a
square-integrable function convolved with a bounded integrable kernel. Boundedness is only
used to make the pointwise averaging integrals well-defined; it does not enter the estimate.
-/

public noncomputable section

open MeasureTheory Real

namespace RegularityStructures.Phi43

theorem integrable_translation_square_weight_product
    {f p : SpaceTime → ℝ} (hf : Measurable f) (hf2 : MemLp f 2)
    (hp : Measurable p) (hp1 : Integrable p) :
    Integrable (fun q : SpaceTime × SpaceTime => f (q.2 - q.1) ^ 2 * |p q.1|)
      ((volume : Measure SpaceTime).prod volume) := by
  have hm : Measurable (fun q : SpaceTime × SpaceTime => f (q.2 - q.1) ^ 2 * |p q.1|) :=
    ((hf.comp (measurable_snd.sub measurable_fst)).pow_const 2).mul
      (hp.comp measurable_fst).norm
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [] with v
    exact ((measurePreserving_sub_right (volume : Measure SpaceTime) v).integrable_comp_of_integrable
      hf2.integrable_sq).mul_const |p v|
  · apply (hp1.norm.const_mul (∫ w : SpaceTime, f w ^ 2)).congr
    filter_upwards [] with v
    symm
    calc
      _ = ∫ w : SpaceTime, f (w - v) ^ 2 * |p v| := by
        apply integral_congr_ae
        filter_upwards [] with w
        exact Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (abs_nonneg _))
      _ = (∫ w : SpaceTime, f w ^ 2) * |p v| := by
        rw [integral_mul_const,
          integral_sub_right_eq_self (μ := volume) (fun w => f w ^ 2) v]

theorem integral_convolution_sq_le_abs_mass_sq
    {f p : SpaceTime → ℝ} (hf : Measurable f) (hf2 : MemLp f 2)
    (hp : Measurable p) (hp1 : Integrable p) {B : ℝ} (hpB : ∀ v, |p v| ≤ B) :
    (∫ w : SpaceTime, (∫ v : SpaceTime, f (w - v) * p v) ^ 2) ≤
      (∫ v : SpaceTime, |p v|) ^ 2 * ∫ w : SpaceTime, f w ^ 2 := by
  have hp2 : MemLp p 2 := by
    apply (memLp_two_iff_integrable_sq hp.aestronglyMeasurable).mpr
    have hi := hp1.mul_bdd hp.aestronglyMeasurable
      (Filter.Eventually.of_forall fun v => by simpa only [Real.norm_eq_abs] using hpB v)
    simpa only [pow_two] using hi
  have hshift (w : SpaceTime) : MemLp (fun v => f (w - v)) 2 :=
    memLp_comp_sub_left_spaceTime hf2 w
  have hpoint (w : SpaceTime) :
      (∫ v : SpaceTime, f (w - v) * p v) ^ 2 ≤
        (∫ v : SpaceTime, |p v|) * ∫ v : SpaceTime, f (w - v) ^ 2 * |p v| := by
    apply integral_mul_sq_le_abs_mass hp1 ((hshift w).integrable_mul hp2)
    apply (hshift w).integrable_sq.mul_bdd hp.norm.aestronglyMeasurable
    filter_upwards [] with v
    simpa only [Real.norm_eq_abs, abs_abs] using hpB v
  have hprod := integrable_translation_square_weight_product hf hf2 hp hp1
  have hmajor : Integrable (fun w : SpaceTime =>
      (∫ v : SpaceTime, |p v|) * ∫ v : SpaceTime, f (w - v) ^ 2 * |p v|) :=
    hprod.swap.integral_prod_left.const_mul _
  have hconv : Measurable (fun w : SpaceTime => ∫ v : SpaceTime, f (w - v) * p v) :=
    (((hf.comp (measurable_fst.sub measurable_snd)).mul
      (hp.comp measurable_snd)).stronglyMeasurable.integral_prod_right').measurable
  have hconv2 : Integrable (fun w : SpaceTime =>
      (∫ v : SpaceTime, f (w - v) * p v) ^ 2) := by
    apply hmajor.mono' (hconv.pow_const 2).aestronglyMeasurable
    filter_upwards [] with w
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hpoint w
  calc
    _ ≤ ∫ w : SpaceTime,
        (∫ v : SpaceTime, |p v|) * ∫ v : SpaceTime, f (w - v) ^ 2 * |p v| :=
      integral_mono hconv2 hmajor hpoint
    _ = (∫ v : SpaceTime, |p v|) *
        (∫ v : SpaceTime, ∫ w : SpaceTime, f (w - v) ^ 2 * |p v|) := by
      rw [integral_const_mul]
      congr 1
      exact integral_integral_swap (f := fun w v : SpaceTime => f (w - v) ^ 2 * |p v|)
        hprod.swap
    _ = (∫ v : SpaceTime, |p v|) ^ 2 * ∫ w : SpaceTime, f w ^ 2 := by
      have htrans (v : SpaceTime) : (∫ w : SpaceTime, f (w - v) ^ 2) =
          ∫ w : SpaceTime, f w ^ 2 :=
        integral_sub_right_eq_self (μ := volume) (fun w => f w ^ 2) v
      simp_rw [integral_mul_const, htrans]
      rw [integral_const_mul]
      ring

theorem integral_add_averaging_sq_le_abs_mass_sq
    {f p : SpaceTime → ℝ} (hf : Measurable f) (hf2 : MemLp f 2)
    (hp : Measurable p) (hp1 : Integrable p) {B : ℝ} (hpB : ∀ v, |p v| ≤ B) :
    (∫ w : SpaceTime, (∫ v : SpaceTime, f (w + v) * p v) ^ 2) ≤
      (∫ v : SpaceTime, |p v|) ^ 2 * ∫ w : SpaceTime, f w ^ 2 := by
  have hinner (w : SpaceTime) : (∫ v : SpaceTime, f (w + v) * p v) =
      ∫ v : SpaceTime, f (w - v) * p (-v) := by
    have h := integral_neg_eq_self (fun v : SpaceTime => f (w + v) * p v)
      (μ := volume)
    simpa only [sub_eq_add_neg] using h.symm
  calc
    _ = ∫ w : SpaceTime, (∫ v : SpaceTime, f (w - v) * p (-v)) ^ 2 := by
      simp_rw [hinner]
    _ ≤ (∫ v : SpaceTime, |p (-v)|) ^ 2 * ∫ w : SpaceTime, f w ^ 2 :=
      integral_convolution_sq_le_abs_mass_sq hf hf2 (hp.comp measurable_neg) hp1.comp_neg
        (fun v => hpB (-v))
    _ = (∫ v : SpaceTime, |p v|) ^ 2 * ∫ w : SpaceTime, f w ^ 2 := by
      rw [integral_neg_eq_self (fun v : SpaceTime => |p v|) (μ := volume)]

end RegularityStructures.Phi43

end
