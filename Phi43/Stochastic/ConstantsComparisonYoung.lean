/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsComparisonConvolution
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import RegularityStructures.Probability.AnnealedNoiseBridge

/-!
# A signed Young estimate on `ℝ × T³`

The comparison of the constants needs the `L¹ * Lᵖ → Lᵖ` estimate for a signed periodised
mollifier.  The library's convolution file supplies the pointwise Hölder
estimate but not this global Young estimate, so it is proved here from Hölder,
Fubini, and translation invariance.  No positivity of the kernel is used.
-/

@[expose] public noncomputable section

open MeasureTheory Filter

namespace RegularityStructures.Phi43

private theorem constantsComparison_holder_positive {p q : ℝ}
    (h : p.HolderConjugate q) : 0 < p ∧ 0 < q := by
  constructor
  · have hp := Real.holderConjugate_iff.mp h
    linarith [hp.1]
  · have hs := Real.holderConjugate_iff.mp h.symm
    linarith [hs.1]

private theorem constantsComparison_memLp_kernel_rpow
    {k : SpaceTime → ℝ} (hk : Measurable k) (hki : Integrable k)
    {q : ℝ} (hq : 0 < q) :
    MemLp (fun y => |k y| ^ (1 / q)) (ENNReal.ofReal q) := by
  have hq0 : ENNReal.ofReal q ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hq)
  have hqt : ENNReal.ofReal q ≠ ⊤ := ENNReal.ofReal_ne_top
  apply (integrable_norm_rpow_iff ((hk.norm.pow_const _).aestronglyMeasurable)
    hq0 hqt).mp
  convert hki.norm using 1
  funext y
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_mul (norm_nonneg _), ENNReal.toReal_ofReal hq.le,
    one_div_mul_cancel (ne_of_gt hq), Real.rpow_one]

private theorem constantsComparison_memLp_weighted_rpow
    {k g : SpaceTime → ℝ} {x : SpaceTime}
    {p : ℝ} (hp : 0 < p) (hk : Measurable k) (hg : Measurable g)
    (hweighted : Integrable (fun y => |k y| * |g (x - y)| ^ p)) :
    MemLp (fun y => |k y| ^ (1 / p) * |g (x - y)|) (ENNReal.ofReal p) := by
  have hp0 : ENNReal.ofReal p ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hp)
  have hpt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hgshift : Measurable (fun y : SpaceTime => g (x - y)) :=
    hg.comp (measurable_const.sub measurable_id)
  apply (integrable_norm_rpow_iff
    (((hk.norm.pow_const _).mul hgshift.norm).aestronglyMeasurable) hp0 hpt).mp
  convert hweighted using 1
  funext y
  simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), abs_abs]
  rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg _) _) (abs_nonneg _),
    ← Real.rpow_mul (abs_nonneg _), ENNReal.toReal_ofReal hp.le,
    one_div_mul_cancel (ne_of_gt hp), Real.rpow_one]

private theorem constantsComparison_holder_integrand_eq
    {k g : SpaceTime → ℝ} {x : SpaceTime} {p q : ℝ}
    (hpq : p.HolderConjugate q) :
    (fun y => (|k y| ^ (1 / p) * |g (x - y)|) * |k y| ^ (1 / q)) =ᵐ[volume]
      (fun y => |k y| * |g (x - y)|) := by
  obtain ⟨hp, hq⟩ := constantsComparison_holder_positive hpq
  filter_upwards [] with y
  by_cases hy : |k y| = 0
  · have hpz : (0 : ℝ) ^ p⁻¹ = 0 :=
      Real.zero_rpow (ne_of_gt (inv_pos.mpr hp))
    have hqz : (0 : ℝ) ^ q⁻¹ = 0 :=
      Real.zero_rpow (ne_of_gt (inv_pos.mpr hq))
    simp [hy, hpz, hqz]
  · have hkne : k y ≠ 0 := by
      intro hk0
      apply hy
      simp [hk0]
    have hypos : 0 < |k y| := abs_pos.mpr hkne
    rw [mul_assoc, mul_comm (|g (x - y)|) _, ← mul_assoc,
      ← Real.rpow_add hypos]
    have hsum : 1 / p + 1 / q = 1 := by
      simpa only [one_div] using hpq.inv_add_inv_eq_one
    rw [hsum, Real.rpow_one]

private theorem constantsComparison_holder_pointwise
    {k g : SpaceTime → ℝ} {x : SpaceTime} {p q : ℝ}
    (hpq : p.HolderConjugate q) (hk : Measurable k) (hki : Integrable k)
    (hg : Measurable g)
    (hweighted : Integrable (fun y => |k y| * |g (x - y)| ^ p)) :
    |spaceTimeConvolution k g x| ^ p ≤
      (∫ y, |k y|) ^ (p - 1) * ∫ y, |k y| * |g (x - y)| ^ p := by
  obtain ⟨hp, hq⟩ := constantsComparison_holder_positive hpq
  have hka := constantsComparison_memLp_kernel_rpow hk hki hq
  have hgb := constantsComparison_memLp_weighted_rpow hp hk hg hweighted
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := (volume : Measure SpaceTime)) hpq
    (Filter.Eventually.of_forall fun y =>
      mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (abs_nonneg _))
    (Filter.Eventually.of_forall fun y => Real.rpow_nonneg (abs_nonneg _) _)
    hgb hka
  have hholder' : ∫ y, |k y| * |g (x - y)| ≤
      (∫ y, |k y| * |g (x - y)| ^ p) ^ (1 / p) *
        (∫ y, |k y|) ^ (1 / q) := by
    have hgb_integral :
        (∫ y, (|k y| ^ (1 / p) * |g (x - y)|) ^ p) =
          ∫ y, |k y| * |g (x - y)| ^ p := by
      apply integral_congr_ae
      filter_upwards [] with y
      simp only [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg _) _)
        (abs_nonneg _)]
      rw [← Real.rpow_mul (abs_nonneg _), one_div_mul_cancel (ne_of_gt hp),
        Real.rpow_one]
    have hka_integral :
        (∫ y, (|k y| ^ (1 / q)) ^ q) = ∫ y, |k y| := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [← Real.rpow_mul (abs_nonneg _), one_div_mul_cancel (ne_of_gt hq),
        Real.rpow_one]
    rw [hgb_integral, hka_integral] at hholder
    rw [← integral_congr_ae (constantsComparison_holder_integrand_eq hpq)]
    simpa only using hholder
  have habs : |spaceTimeConvolution k g x| ≤
      ∫ y, |k y| * |g (x - y)| := by
    calc
      |spaceTimeConvolution k g x| =
          |∫ y, k y * g (x - y)| := rfl
      _ ≤ ∫ y, |k y * g (x - y)| := by
        have hni := norm_integral_le_integral_norm
          (μ := (volume : Measure SpaceTime))
          (fun y : SpaceTime => k y * g (x - y))
        simpa only [Real.norm_eq_abs] using hni
      _ = ∫ y, |k y| * |g (x - y)| := by
        apply integral_congr_ae
        filter_upwards [] with y
        rw [abs_mul]
  have hnonnegA : 0 ≤ ∫ y, |k y| := integral_nonneg_of_ae
    (Eventually.of_forall fun y => abs_nonneg _)
  have hnonnegW : 0 ≤ ∫ y, |k y| * |g (x - y)| ^ p := integral_nonneg_of_ae
    (Eventually.of_forall fun y => mul_nonneg (abs_nonneg _)
      (Real.rpow_nonneg (abs_nonneg _) _))
  have hpower :
      ((∫ y, |k y| * |g (x - y)| ^ p) ^ (1 / p) *
        (∫ y, |k y|) ^ (1 / q)) ^ p =
      (∫ y, |k y|) ^ (p - 1) *
        ∫ y, |k y| * |g (x - y)| ^ p := by
    rw [Real.mul_rpow (Real.rpow_nonneg hnonnegW _) (Real.rpow_nonneg hnonnegA _),
      ← Real.rpow_mul hnonnegW, ← Real.rpow_mul hnonnegA,
      one_div_mul_cancel (ne_of_gt hp)]
    rw [Real.rpow_one]
    rw [show (1 / q : ℝ) * p = p / q by ring]
    rw [hpq.div_conj_eq_sub_one]
    ring
  have hbound := Real.rpow_le_rpow
    (integral_nonneg_of_ae (Eventually.of_forall fun y =>
      mul_nonneg (abs_nonneg _) (abs_nonneg _))) hholder' (le_of_lt hp)
  exact ((Real.rpow_le_rpow (abs_nonneg _) habs (le_of_lt hp)).trans hbound).trans_eq
    hpower

theorem constantsComparison_spaceTimeConvolution_Lp_integrable
    {k g : SpaceTime → ℝ} {p q : ℝ} (hpq : p.HolderConjugate q)
    (hk : Measurable k) (hki : Integrable k) (hg : Measurable g)
    (hconv : ∀ᵐ x ∂(volume : Measure SpaceTime),
      Integrable (fun y => k y * g (x - y)))
    (hweighted : Integrable (fun z : SpaceTime × SpaceTime =>
      |k z.2| * |g (z.1 - z.2)| ^ p)
      ((volume : Measure SpaceTime).prod volume)) :
    Integrable (fun x => |spaceTimeConvolution k g x| ^ p) ∧
      ∫ x, |spaceTimeConvolution k g x| ^ p ≤
        (∫ y, |k y|) ^ (p - 1) * ∫ z : SpaceTime × SpaceTime,
          |k z.2| * |g (z.1 - z.2)| ^ p := by
  let μ : Measure SpaceTime := volume
  obtain ⟨hp, _hq⟩ := constantsComparison_holder_positive hpq
  have hleft : Integrable (fun x : SpaceTime =>
      ∫ y, |k y| * |g (x - y)| ^ p) μ :=
    hweighted.integral_prod_left
  have hA : 0 ≤ ∫ y, |k y| := integral_nonneg_of_ae
    (Eventually.of_forall fun y => abs_nonneg _)
  have hupper : Integrable (fun x : SpaceTime =>
      (∫ y, |k y|) ^ (p - 1) * ∫ y, |k y| * |g (x - y)| ^ p)
      μ := by
    exact hleft.const_mul _
  have hconv_meas : AEStronglyMeasurable (spaceTimeConvolution k g)
      μ := by
    change AEStronglyMeasurable
      (MeasureTheory.convolution k g (ContinuousLinearMap.lsmul ℝ ℝ) volume) μ
    exact hk.aestronglyMeasurable.convolution
      (ContinuousLinearMap.lsmul ℝ ℝ) hg.aestronglyMeasurable
  have hpoint : ∀ᵐ x ∂μ,
      |spaceTimeConvolution k g x| ^ p ≤
        (∫ y, |k y|) ^ (p - 1) * ∫ y, |k y| * |g (x - y)| ^ p := by
    filter_upwards [hconv, hweighted.prod_right_ae] with x hcx hwx
    exact constantsComparison_holder_pointwise hpq hk hki hg hwx
  have hint : Integrable (fun x => |spaceTimeConvolution k g x| ^ p) μ := by
    have hpow_meas : AEStronglyMeasurable
        (fun x => |spaceTimeConvolution k g x| ^ p) μ := by
      simpa only [Function.comp_def, Real.norm_eq_abs] using
        (hconv_meas.norm.aemeasurable.pow_const p).aestronglyMeasurable
    refine hupper.mono hpow_meas ?_
    filter_upwards [hpoint] with x hx
    have hleft' : 0 ≤ |spaceTimeConvolution k g x| ^ p :=
      Real.rpow_nonneg (abs_nonneg _) _
    have hright' : 0 ≤ (∫ y, |k y|) ^ (p - 1) *
        ∫ y, |k y| * |g (x - y)| ^ p :=
      mul_nonneg (Real.rpow_nonneg hA _) (integral_nonneg_of_ae
        (Eventually.of_forall fun y => mul_nonneg (abs_nonneg _)
          (Real.rpow_nonneg (abs_nonneg _) _)))
    simpa only [Real.norm_eq_abs, abs_of_nonneg hleft', abs_of_nonneg hright']
      using hx
  refine ⟨hint, ?_⟩
  calc
    ∫ x, |spaceTimeConvolution k g x| ^ p ∂μ ≤
        ∫ x, (∫ y, |k y|) ^ (p - 1) *
          ∫ y, |k y| * |g (x - y)| ^ p :=
      integral_mono_ae hint hupper hpoint
    _ = (∫ y, |k y|) ^ (p - 1) *
        ∫ z : SpaceTime × SpaceTime,
          |k z.2| * |g (z.1 - z.2)| ^ p := by
      rw [integral_const_mul]
      rw [Measure.volume_eq_prod SpaceTime SpaceTime]
      rw [integral_integral hweighted]

end RegularityStructures.Phi43

end
