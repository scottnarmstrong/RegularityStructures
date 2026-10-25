/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsComparisonFramework
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Phi43.Stochastic.ConstantsComparisonApproxLp
public import Phi43.Stochastic.ConstantsComparisonHairerMollifiedBound
public import Phi43.Stochastic.ConstantsComparisonKernelMemLp
public import Phi43.Stochastic.ConstantsComparisonRemainderMemLp
public import RegularityStructures.Probability.AnnealedNoiseBridge

/-!
# A scale-uniform covariance comparison

The fixed-scale covariance comparison is strengthened here by applying the signed Young estimate
to the unregularised order-one remainder and the two unregularised order-three kernels.  The
periodised mollifier has scale-independent total variation, so the resulting bound is uniform in
`ε`.  This is the bounded covariance difference required in the comparison of the constants.
-/

@[expose] public noncomputable section

open MeasureTheory Filter

namespace RegularityStructures.Phi43

private theorem covarianceComparison_holder_4_4over3_uniform :
    (4 : ℝ).HolderConjugate (4 / 3 : ℝ) := by
  apply Real.holderConjugate_iff.mpr
  constructor <;> norm_num

private theorem covarianceComparison_lpNorm_eq_toReal_eLpNorm_uniform
    {f : SpaceTime → ℝ} {p : ℝ} (hp : 1 < p)
    (hf : MemLp f (ENNReal.ofReal p)) :
    constantsComparisonLpNorm f p =
      (eLpNorm f (ENNReal.ofReal p)).toReal := by
  have hpPos : 0 < p := lt_trans zero_lt_one hp
  have hp0 : 0 ≤ p := hpPos.le
  have hroot := hf.eLpNorm_eq_integral_rpow_norm
    (ne_of_gt (ENNReal.ofReal_pos.mpr hpPos)) (by exact ENNReal.ofReal_ne_top)
  unfold constantsComparisonLpNorm
  rw [hroot]
  rw [ENNReal.toReal_ofReal]
  · simp only [ENNReal.toReal_ofReal hp0, Real.norm_eq_abs, one_div]
  · positivity

private theorem constantsComparisonLpNorm_nonneg_uniform {f : SpaceTime → ℝ} {p : ℝ} :
    0 ≤ constantsComparisonLpNorm f p := by
  unfold constantsComparisonLpNorm
  exact Real.rpow_nonneg
    (integral_nonneg_of_ae (Eventually.of_forall fun z =>
      Real.rpow_nonneg (norm_nonneg _) _)) _

private theorem covarianceComparison_periodise_convolution_integrable_of_integrable_uniform
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    {f : SpaceTime → ℝ} (hf : Integrable f) (_hfmeas : Measurable f) :
    ∀ z : SpaceTime, Integrable (fun w : SpaceTime => periodise ρ ε w * f (z - w)) := by
  obtain ⟨CP, hCP⟩ := bounded_periodise ρ hρ hε
  let DP : ℝ := max CP 0
  have htop : MemLp (periodise ρ ε) ⊤ :=
    memLp_top_of_bound (measurable_periodise ρ hρ).aestronglyMeasurable DP
      (Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs] using (hCP z).trans (le_max_left CP 0))
  have hone : MemLp f 1 := memLp_one_iff_integrable.mpr hf
  intro z
  have hshift : MemLp (fun w : SpaceTime => f (z - w)) 1 := by
    apply memLp_one_iff_integrable.mpr
    exact integrable_comp_sub_left_spaceTime hf z
  have hmul := htop.integrable_mul hshift
  change Integrable ((fun w : SpaceTime => periodise ρ ε w) *
    (fun w => f (z - w))) at hmul
  exact hmul

private theorem covarianceComparison_periodise_convolution_lpNorm_le
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {ε p q : ℝ} (hε : 0 < ε) (hpq : p.HolderConjugate q)
    {f : SpaceTime → ℝ} (hf : MemLp f (ENNReal.ofReal p)) (hfmeas : Measurable f) :
    constantsComparisonLpNorm (spaceTimeConvolution (periodise ρ ε) f) p ≤
      (∫ y, |periodise ρ ε y|) * constantsComparisonLpNorm f p := by
  have hmass : 0 < ∫ y : SpaceTime, |periodise ρ ε y| := by
    have habs := abs_integral_le_integral_abs (f := periodise ρ ε)
      (μ := (volume : Measure SpaceTime))
    rw [constantsComparison_periodise_mass ρ hρ hε] at habs
    exact lt_of_lt_of_le zero_lt_one (by simpa using habs)
  have hconv := constantsComparison_periodise_convolution_exists ρ hρ hε hpq hf
  have hconv_ae : ∀ᵐ x : SpaceTime ∂(volume : Measure SpaceTime),
      Integrable (fun y => periodise ρ ε y * f (x - y)) :=
    Eventually.of_forall fun x => hconv x
  have hbound := constantsComparison_spaceTimeConvolution_eLpNorm_le
    (k := periodise ρ ε) (f := f) (p := p) (q := q) hpq
    (measurable_periodise ρ hρ) (integrable_periodise ρ hρ hε) hfmeas hmass
    hconv_ae hf
  have hTmem : MemLp (spaceTimeConvolution (periodise ρ ε) f)
      (ENNReal.ofReal p) := by
    exact memLp_iff.mpr (lt_of_le_of_lt hbound (by finiteness))
  have hreal := ENNReal.toReal_mono (by finiteness) hbound
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hmass.le] at hreal
  rw [← covarianceComparison_lpNorm_eq_toReal_eLpNorm_uniform hpq.lt hTmem] at hreal
  rw [← covarianceComparison_lpNorm_eq_toReal_eLpNorm_uniform hpq.lt hf] at hreal
  exact hreal

private theorem covarianceComparison_periodise_convolution_memLp_uniform
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {ε p q : ℝ} (hε : 0 < ε) (hpq : p.HolderConjugate q)
    {f : SpaceTime → ℝ} (hf : MemLp f (ENNReal.ofReal p)) (hfmeas : Measurable f) :
    MemLp (spaceTimeConvolution (periodise ρ ε) f) (ENNReal.ofReal p) := by
  have hmass : 0 < ∫ y : SpaceTime, |periodise ρ ε y| := by
    have habs := abs_integral_le_integral_abs (f := periodise ρ ε)
      (μ := (volume : Measure SpaceTime))
    rw [constantsComparison_periodise_mass ρ hρ hε] at habs
    exact lt_of_lt_of_le zero_lt_one (by simpa using habs)
  have hconv := constantsComparison_periodise_convolution_exists ρ hρ hε hpq hf
  have hconv_ae : ∀ᵐ x : SpaceTime ∂(volume : Measure SpaceTime),
      Integrable (fun y => periodise ρ ε y * f (x - y)) :=
    Eventually.of_forall fun x => hconv x
  have hbound := constantsComparison_spaceTimeConvolution_eLpNorm_le
    (k := periodise ρ ε) (f := f) (p := p) (q := q) hpq
    (measurable_periodise ρ hρ) (integrable_periodise ρ hρ hε) hfmeas hmass
    hconv_ae hf
  exact memLp_iff.mpr (lt_of_le_of_lt hbound (by finiteness))

private theorem covarianceComparison_R_mollified_memLp_uniform
    (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε) :
    MemLp (wickComparisonR N ρ ε) (ENNReal.ofReal 4) := by
  have hR : MemLp (constantsComparisonR N) (ENNReal.ofReal 4) :=
    constantsComparisonR_memLp_four N
  have hconv := covarianceComparison_periodise_convolution_memLp_uniform ρ hρ hε
    covarianceComparison_holder_4_4over3_uniform hR
    (measurable_massiveHeatKernel.sub (measurable_constantsComparison_hairerKernelTorus N))
  have hR_eq : spaceTimeConvolution (periodise ρ ε) (constantsComparisonR N) =
      wickComparisonR N ρ ε := by
    have hGint := covarianceComparison_periodise_convolution_integrable_of_integrable_uniform
      ρ hρ hε integrable_massiveHeatKernel measurable_massiveHeatKernel
    have hKint := covarianceComparison_periodise_convolution_integrable_of_integrable_uniform
      ρ hρ hε (integrable_constantsComparison_hairerKernelTorus N)
      (measurable_constantsComparison_hairerKernelTorus N)
    funext z
    change (∫ w, periodise ρ ε w *
        (massiveHeatKernel (z - w) - hairerKernelTorus N (z - w))) = _
    calc
      (∫ w, periodise ρ ε w *
          (massiveHeatKernel (z - w) - hairerKernelTorus N (z - w))) =
          (∫ w, periodise ρ ε w * massiveHeatKernel (z - w)) -
            ∫ w, periodise ρ ε w * hairerKernelTorus N (z - w) := by
        rw [← integral_sub (hGint z) (hKint z)]
        apply integral_congr_ae
        filter_upwards [] with w
        ring
      _ = spaceTimeConvolution (periodise ρ ε) massiveHeatKernel z -
          spaceTimeConvolution (periodise ρ ε) (hairerKernelTorus N) z := by
        rfl
      _ = wickComparisonR N ρ ε z := by
        rw [constantsComparison_mollifiedKernel_eq_convolution ρ,
          constantsComparison_hairerMollifiedKernel_eq_convolution N ρ]
        rfl
  rw [← hR_eq]
  exact hconv

private theorem covarianceComparison_G_mollified_memLp_uniform
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε) :
    MemLp (mollifiedKernel ρ ε) (ENNReal.ofReal (4 / 3 : ℝ)) := by
  have hG : MemLp massiveHeatKernel (ENNReal.ofReal (4 / 3 : ℝ)) :=
    constantsComparison_massiveHeatKernel_memLp_fourThirds
  have hconv := covarianceComparison_periodise_convolution_memLp_uniform ρ hρ hε
    covarianceComparison_holder_4_4over3_uniform.symm hG measurable_massiveHeatKernel
  rw [← constantsComparison_mollifiedKernel_eq_convolution ρ]
  exact hconv

private theorem covarianceComparison_K_mollified_memLp_uniform
    (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε) :
    MemLp (hairerMollifiedKernel N ρ ε) (ENNReal.ofReal (4 / 3 : ℝ)) := by
  have hK : MemLp (hairerKernelTorus N) (ENNReal.ofReal (4 / 3 : ℝ)) :=
    constantsComparison_hairerKernelTorus_memLp_fourThirds N
  have hconv := covarianceComparison_periodise_convolution_memLp_uniform ρ hρ hε
    covarianceComparison_holder_4_4over3_uniform.symm hK
    (measurable_constantsComparison_hairerKernelTorus N)
  rw [← constantsComparison_hairerMollifiedKernel_eq_convolution N ρ]
  exact hconv

private theorem covarianceComparison_uniform_mollified_norms
    (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    constantsComparisonLpNorm (wickComparisonR N ρ ε) 4 ≤
        (∫ y : ParabolicSpace, |ρ y|) *
          constantsComparisonLpNorm (constantsComparisonR N) 4 ∧
    constantsComparisonLpNorm (mollifiedKernel ρ ε) (4 / 3 : ℝ) ≤
        (∫ y : ParabolicSpace, |ρ y|) *
          constantsComparisonLpNorm massiveHeatKernel (4 / 3 : ℝ) ∧
    constantsComparisonLpNorm (hairerMollifiedKernel N ρ ε) (4 / 3 : ℝ) ≤
        (∫ y : ParabolicSpace, |ρ y|) *
          constantsComparisonLpNorm (hairerKernelTorus N) (4 / 3 : ℝ) := by
  have hpq := covarianceComparison_holder_4_4over3_uniform
  have hpq' := hpq.symm
  have hmass : ∫ z : SpaceTime, |periodise ρ ε z| ≤
      ∫ y : ParabolicSpace, |ρ y| := by
    exact (integral_abs_periodise_le ρ hρ hε hε1).trans_eq (integral_abs_rescale ρ hε)
  have hR : MemLp (constantsComparisonR N) (ENNReal.ofReal 4) :=
    constantsComparisonR_memLp_four N
  have hRmeas : Measurable (constantsComparisonR N) :=
    measurable_massiveHeatKernel.sub (measurable_constantsComparison_hairerKernelTorus N)
  have hRconv := covarianceComparison_periodise_convolution_lpNorm_le
    ρ hρ hε hpq hR hRmeas
  have hG : MemLp massiveHeatKernel (ENNReal.ofReal (4 / 3 : ℝ)) :=
    constantsComparison_massiveHeatKernel_memLp_fourThirds
  have hGconv := covarianceComparison_periodise_convolution_lpNorm_le
    ρ hρ hε hpq' hG measurable_massiveHeatKernel
  have hK : MemLp (hairerKernelTorus N) (ENNReal.ofReal (4 / 3 : ℝ)) :=
    constantsComparison_hairerKernelTorus_memLp_fourThirds N
  have hKmeas := measurable_constantsComparison_hairerKernelTorus N
  have hKconv := covarianceComparison_periodise_convolution_lpNorm_le
    ρ hρ hε hpq' hK hKmeas
  have hRconv' : constantsComparisonLpNorm
      (spaceTimeConvolution (periodise ρ ε) (constantsComparisonR N)) 4 ≤
      (∫ y : ParabolicSpace, |ρ y|) * constantsComparisonLpNorm
        (constantsComparisonR N) 4 := by
    exact hRconv.trans (mul_le_mul_of_nonneg_right hmass
      (constantsComparisonLpNorm_nonneg_uniform (f := constantsComparisonR N) (p := 4)))
  have hGconv' : constantsComparisonLpNorm
      (spaceTimeConvolution (periodise ρ ε) massiveHeatKernel) (4 / 3 : ℝ) ≤
      (∫ y : ParabolicSpace, |ρ y|) * constantsComparisonLpNorm massiveHeatKernel
        (4 / 3 : ℝ) := by
    exact hGconv.trans (mul_le_mul_of_nonneg_right hmass
      (constantsComparisonLpNorm_nonneg_uniform (f := massiveHeatKernel)
        (p := (4 / 3 : ℝ))))
  have hKconv' : constantsComparisonLpNorm
      (spaceTimeConvolution (periodise ρ ε) (hairerKernelTorus N)) (4 / 3 : ℝ) ≤
      (∫ y : ParabolicSpace, |ρ y|) * constantsComparisonLpNorm (hairerKernelTorus N)
        (4 / 3 : ℝ) := by
    exact hKconv.trans (mul_le_mul_of_nonneg_right hmass
      (constantsComparisonLpNorm_nonneg_uniform (f := hairerKernelTorus N)
        (p := (4 / 3 : ℝ))))
  have hR_eq : spaceTimeConvolution (periodise ρ ε) (constantsComparisonR N) =
      wickComparisonR N ρ ε := by
    change spaceTimeConvolution (periodise ρ ε)
        (massiveHeatKernel - hairerKernelTorus N) = _
    have hGint := covarianceComparison_periodise_convolution_integrable_of_integrable_uniform
      ρ hρ hε integrable_massiveHeatKernel measurable_massiveHeatKernel
    have hKint := covarianceComparison_periodise_convolution_integrable_of_integrable_uniform
      ρ hρ hε (integrable_constantsComparison_hairerKernelTorus N) hKmeas
    funext z
    change (∫ w, periodise ρ ε w *
        (massiveHeatKernel (z - w) - hairerKernelTorus N (z - w))) = _
    calc
      (∫ w, periodise ρ ε w *
          (massiveHeatKernel (z - w) - hairerKernelTorus N (z - w))) =
          (∫ w, periodise ρ ε w * massiveHeatKernel (z - w)) -
            ∫ w, periodise ρ ε w * hairerKernelTorus N (z - w) := by
        rw [← integral_sub (hGint z) (hKint z)]
        apply integral_congr_ae
        filter_upwards [] with w
        ring
      _ = spaceTimeConvolution (periodise ρ ε) massiveHeatKernel z -
          spaceTimeConvolution (periodise ρ ε) (hairerKernelTorus N) z := by
        rfl
      _ = wickComparisonR N ρ ε z := by
        rw [constantsComparison_mollifiedKernel_eq_convolution ρ,
          constantsComparison_hairerMollifiedKernel_eq_convolution N ρ]
        rfl
  have hG_eq : spaceTimeConvolution (periodise ρ ε) massiveHeatKernel =
      mollifiedKernel ρ ε := constantsComparison_mollifiedKernel_eq_convolution ρ
  have hK_eq : spaceTimeConvolution (periodise ρ ε) (hairerKernelTorus N) =
      hairerMollifiedKernel N ρ ε :=
    constantsComparison_hairerMollifiedKernel_eq_convolution N ρ
  refine ⟨?_, ?_, ?_⟩
  · rw [← hR_eq]
    exact hRconv'
  · rw [← hG_eq]
    exact hGconv'
  · rw [← hK_eq]
    exact hKconv'

theorem constantsComparison_covariance_difference_uniform_bound_unconditional
    (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ z : SpaceTime,
      |covariance ρ ε z - hairerCovariance N ρ ε z| ≤ C := by
  let Bmass : ℝ := ∫ y : ParabolicSpace, |ρ y|
  let aR : ℝ := constantsComparisonLpNorm (constantsComparisonR N) 4
  let aG : ℝ := constantsComparisonLpNorm massiveHeatKernel (4 / 3 : ℝ)
  let aK : ℝ := constantsComparisonLpNorm (hairerKernelTorus N) (4 / 3 : ℝ)
  let C : ℝ := Bmass ^ 2 * aR * (aG + aK)
  have hBmass : 0 ≤ Bmass := by
    dsimp [Bmass]
    exact integral_nonneg_of_ae (Eventually.of_forall fun y => abs_nonneg _)
  have haR : 0 ≤ aR := by exact constantsComparisonLpNorm_nonneg_uniform
  have haG : 0 ≤ aG := by exact constantsComparisonLpNorm_nonneg_uniform
  have haK : 0 ≤ aK := by exact constantsComparisonLpNorm_nonneg_uniform
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro ε hε hε1 z
  obtain ⟨hRε, hGε, hKε⟩ :=
    covarianceComparison_uniform_mollified_norms N ρ hρ hε hε1
  have hRmem : MemLp (wickComparisonR N ρ ε) (ENNReal.ofReal 4) :=
    covarianceComparison_R_mollified_memLp_uniform N ρ hρ hε
  have hGmem : MemLp (mollifiedKernel ρ ε) (ENNReal.ofReal (4 / 3 : ℝ)) :=
    covarianceComparison_G_mollified_memLp_uniform ρ hρ hε
  have hKmem : MemLp (hairerMollifiedKernel N ρ ε)
      (ENNReal.ofReal (4 / 3 : ℝ)) :=
    covarianceComparison_K_mollified_memLp_uniform N ρ hρ hε
  have hRshift : MemLp (fun w : SpaceTime => wickComparisonR N ρ ε (z + w))
      (ENNReal.ofReal 4) :=
    hRmem.comp_measurePreserving (measurePreserving_add_left volume z)
  have hKshift : MemLp
      (fun w : SpaceTime => hairerMollifiedKernel N ρ ε (z + w))
      (ENNReal.ofReal (4 / 3 : ℝ)) :=
    hKmem.comp_measurePreserving (measurePreserving_add_left volume z)
  have hcross1 : Integrable (fun w =>
      wickComparisonR N ρ ε (z + w) * mollifiedKernel ρ ε w) := by
    have hs := @MemLp.integrable_mul SpaceTime _ volume ℝ _
      (ENNReal.ofReal 4) (ENNReal.ofReal (4 / 3 : ℝ)) _ _
      hRshift hGmem covarianceComparison_holder_4_4over3_uniform.ennrealOfReal
    change Integrable ((fun w => wickComparisonR N ρ ε (z + w)) *
      mollifiedKernel ρ ε) at hs
    exact hs
  have hcross2 : Integrable (fun w =>
      hairerMollifiedKernel N ρ ε (z + w) * wickComparisonR N ρ ε w) := by
    have hs := @MemLp.integrable_mul SpaceTime _ volume ℝ _
      (ENNReal.ofReal (4 / 3 : ℝ)) (ENNReal.ofReal 4) _ _
      hKshift hRmem covarianceComparison_holder_4_4over3_uniform.symm.ennrealOfReal
    change Integrable ((fun w => hairerMollifiedKernel N ρ ε (z + w)) *
      wickComparisonR N ρ ε) at hs
    exact hs
  have hcross : Integrable (fun w =>
      wickComparisonR N ρ ε (z + w) * mollifiedKernel ρ ε w +
        hairerMollifiedKernel N ρ ε (z + w) * wickComparisonR N ρ ε w) :=
    hcross1.add hcross2
  have hdiff : covariance ρ ε z - hairerCovariance N ρ ε z =
      ∫ w, wickComparisonR N ρ ε (z + w) * mollifiedKernel ρ ε w +
        hairerMollifiedKernel N ρ ε (z + w) * wickComparisonR N ρ ε w := by
    rw [covariance, hairerCovariance]
    have hGint := (covariance_facts ρ hρ hε).1 z
    have hKint : Integrable (fun w =>
        hairerMollifiedKernel N ρ ε (z + w) * hairerMollifiedKernel N ρ ε w) := by
      have hKbase : Integrable (hairerMollifiedKernel N ρ ε) := by
        rw [← constantsComparison_hairerMollifiedKernel_eq_convolution N ρ]
        exact (integrable_periodise ρ hρ hε).integrable_convolution
          (ContinuousLinearMap.lsmul ℝ ℝ)
          (integrable_constantsComparison_hairerKernelTorus N)
      have hKmeas : AEStronglyMeasurable (hairerMollifiedKernel N ρ ε) volume :=
        hKmem.aestronglyMeasurable
      obtain ⟨B, hB, hbound⟩ := hairerMollifiedKernel_singular_bound ρ hρ N
      have htop : MemLp (hairerMollifiedKernel N ρ ε) ⊤ := by
        apply memLp_top_of_bound hKmeas (B * ε ^ (-(3 : ℝ)))
        filter_upwards [] with y
        have hpos : 0 < torusParabolicSize y + ε :=
          add_pos_of_nonneg_of_pos (torusParabolicSize_nonneg y) hε
        have hpow : (torusParabolicSize y + ε) ^ (-(3 : ℝ)) ≤
            ε ^ (-(3 : ℝ)) := Real.rpow_le_rpow_of_nonpos hε
              (le_add_of_nonneg_left (torusParabolicSize_nonneg y)) (by norm_num)
        have hb := hbound hε hε1 y
        exact (hb.trans (mul_le_mul_of_nonneg_left hpow hB)).trans_eq (by rfl)
      have htopShift : MemLp
          (fun w : SpaceTime => hairerMollifiedKernel N ρ ε (z + w)) ⊤ :=
        htop.comp_measurePreserving (measurePreserving_add_left volume z)
      have hmul := htopShift.integrable_mul
        (memLp_one_iff_integrable.mpr hKbase)
      change Integrable ((fun w => hairerMollifiedKernel N ρ ε (z + w)) *
        hairerMollifiedKernel N ρ ε) at hmul
      exact hmul
    rw [← integral_sub hGint hKint]
    apply integral_congr_ae
    filter_upwards [] with w
    simp only [wickComparisonR]
    ring
  rw [hdiff]
  have hpair1 := integral_mul_norm_le_Lp_mul_Lq
    (p := (4 : ℝ)) (q := (4 / 3 : ℝ))
    covarianceComparison_holder_4_4over3_uniform hRshift hGmem
  have hpair2 := integral_mul_norm_le_Lp_mul_Lq
    (p := (4 / 3 : ℝ)) (q := (4 : ℝ))
    covarianceComparison_holder_4_4over3_uniform.symm hKshift hRmem
  have hRint : (∫ w : SpaceTime, ‖wickComparisonR N ρ ε (z + w)‖ ^ (4 : ℝ)) =
      ∫ w : SpaceTime, ‖wickComparisonR N ρ ε w‖ ^ (4 : ℝ) :=
    integral_comp_add_left_spaceTime
      (fun w : SpaceTime => ‖wickComparisonR N ρ ε w‖ ^ (4 : ℝ)) z
  rw [hRint] at hpair1
  have hKint' : (∫ w, ‖hairerMollifiedKernel N ρ ε (z + w)‖ ^
      (4 / 3 : ℝ)) = ∫ w, ‖hairerMollifiedKernel N ρ ε w‖ ^ (4 / 3 : ℝ) :=
    integral_comp_add_left_spaceTime
      (fun w : SpaceTime => ‖hairerMollifiedKernel N ρ ε w‖ ^
        (4 / 3 : ℝ)) z
  rw [hKint'] at hpair2
  have hpair1' : (∫ w, |wickComparisonR N ρ ε (z + w)| *
      |mollifiedKernel ρ ε w|) ≤
      constantsComparisonLpNorm (wickComparisonR N ρ ε) 4 *
        constantsComparisonLpNorm (mollifiedKernel ρ ε) (4 / 3 : ℝ) := by
    simpa [constantsComparisonLpNorm, Real.norm_eq_abs] using hpair1
  have hpair2' : (∫ w, |hairerMollifiedKernel N ρ ε (z + w)| *
      |wickComparisonR N ρ ε w|) ≤
      constantsComparisonLpNorm (hairerMollifiedKernel N ρ ε) (4 / 3 : ℝ) *
        constantsComparisonLpNorm (wickComparisonR N ρ ε) 4 := by
    simpa [constantsComparisonLpNorm, Real.norm_eq_abs] using hpair2
  have hsum : |∫ w, wickComparisonR N ρ ε (z + w) *
      mollifiedKernel ρ ε w + hairerMollifiedKernel N ρ ε (z + w) *
      wickComparisonR N ρ ε w| ≤
      constantsComparisonLpNorm (wickComparisonR N ρ ε) 4 *
          constantsComparisonLpNorm (mollifiedKernel ρ ε) (4 / 3 : ℝ) +
        constantsComparisonLpNorm (hairerMollifiedKernel N ρ ε) (4 / 3 : ℝ) *
          constantsComparisonLpNorm (wickComparisonR N ρ ε) 4 := by
    calc
      _ ≤ ∫ w, |wickComparisonR N ρ ε (z + w) * mollifiedKernel ρ ε w| +
          |hairerMollifiedKernel N ρ ε (z + w) * wickComparisonR N ρ ε w| := by
        have hnormsum := hcross1.norm.add hcross2.norm
        have hnorm := norm_integral_le_of_norm_le hnormsum
          (Eventually.of_forall fun w => norm_add_le
            (wickComparisonR N ρ ε (z + w) * mollifiedKernel ρ ε w)
            (hairerMollifiedKernel N ρ ε (z + w) * wickComparisonR N ρ ε w))
        simpa only [Pi.add_apply, Real.norm_eq_abs] using hnorm
      _ = (∫ w, |wickComparisonR N ρ ε (z + w)| * |mollifiedKernel ρ ε w|) +
          ∫ w, |hairerMollifiedKernel N ρ ε (z + w)| *
            |wickComparisonR N ρ ε w| := by
        rw [integral_add]
        · apply congrArg₂ (· + ·) <;> apply integral_congr_ae
          · filter_upwards [] with w; rw [abs_mul]
          · filter_upwards [] with w; rw [abs_mul]
        · exact hcross1.norm
        · exact hcross2.norm
      _ ≤ _ := add_le_add hpair1' hpair2'
  have hnorm_bound :
      constantsComparisonLpNorm (wickComparisonR N ρ ε) 4 *
          constantsComparisonLpNorm (mollifiedKernel ρ ε) (4 / 3 : ℝ) +
        constantsComparisonLpNorm (hairerMollifiedKernel N ρ ε) (4 / 3 : ℝ) *
          constantsComparisonLpNorm (wickComparisonR N ρ ε) 4 ≤ C := by
    dsimp [C, Bmass, aR, aG, aK] at hRε hGε hKε ⊢
    have hRε0 : 0 ≤ constantsComparisonLpNorm (wickComparisonR N ρ ε) 4 :=
      constantsComparisonLpNorm_nonneg_uniform
    have hGε0 : 0 ≤ constantsComparisonLpNorm (mollifiedKernel ρ ε) (4 / 3 : ℝ) :=
      constantsComparisonLpNorm_nonneg_uniform
    have hKε0 : 0 ≤ constantsComparisonLpNorm
        (hairerMollifiedKernel N ρ ε) (4 / 3 : ℝ) :=
      constantsComparisonLpNorm_nonneg_uniform
    have hBaR : 0 ≤ (∫ y : ParabolicSpace, |ρ y|) *
        constantsComparisonLpNorm (constantsComparisonR N) 4 :=
      mul_nonneg hBmass haR
    have hBaG : 0 ≤ (∫ y : ParabolicSpace, |ρ y|) *
        constantsComparisonLpNorm massiveHeatKernel (4 / 3 : ℝ) :=
      mul_nonneg hBmass haG
    have hBaK : 0 ≤ (∫ y : ParabolicSpace, |ρ y|) *
        constantsComparisonLpNorm (hairerKernelTorus N) (4 / 3 : ℝ) :=
      mul_nonneg hBmass haK
    calc
      constantsComparisonLpNorm (wickComparisonR N ρ ε) 4 *
          constantsComparisonLpNorm (mollifiedKernel ρ ε) (4 / 3 : ℝ) +
          constantsComparisonLpNorm (hairerMollifiedKernel N ρ ε) (4 / 3 : ℝ) *
            constantsComparisonLpNorm (wickComparisonR N ρ ε) 4 ≤
          ((∫ y : ParabolicSpace, |ρ y|) *
              constantsComparisonLpNorm (constantsComparisonR N) 4) *
            ((∫ y : ParabolicSpace, |ρ y|) *
              constantsComparisonLpNorm massiveHeatKernel (4 / 3 : ℝ)) +
          ((∫ y : ParabolicSpace, |ρ y|) *
              constantsComparisonLpNorm (hairerKernelTorus N) (4 / 3 : ℝ)) *
            ((∫ y : ParabolicSpace, |ρ y|) *
              constantsComparisonLpNorm (constantsComparisonR N) 4) := by
            exact add_le_add
              (le_trans (mul_le_mul_of_nonneg_right hRε hGε0)
                (mul_le_mul_of_nonneg_left hGε hBaR))
              (le_trans (mul_le_mul_of_nonneg_right hKε hRε0)
                (mul_le_mul_of_nonneg_left hRε hBaK))
      _ = (∫ y : ParabolicSpace, |ρ y|) ^ 2 *
          constantsComparisonLpNorm (constantsComparisonR N) 4 *
          (constantsComparisonLpNorm massiveHeatKernel (4 / 3 : ℝ) +
            constantsComparisonLpNorm (hairerKernelTorus N) (4 / 3 : ℝ)) := by ring
  exact (hsum.trans hnorm_bound)

end RegularityStructures.Phi43

end
