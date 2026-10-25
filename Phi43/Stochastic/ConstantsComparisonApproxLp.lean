/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsComparisonConvolution
public import Phi43.Stochastic.ConstantsComparisonMemLp
public import Phi43.ClassicalSolution.PeriodiseRegularity
public import Phi43.Stochastic.ConstantsComparisonApproxIdentity
public import Phi43.Torus.KernelBoundsSupport
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.Support
public import RegularityStructures.Probability.AnnealedNoiseBridge

/-!
# Finite `Lᵖ` inputs for the periodised mollifier

The periodised mollifier is bounded and supported in a compact time strip.  This gives the
finite-`Lᵖ` input needed by the signed Young estimate for every exponent, including the two
exponents used in the Wick-constant comparison.  The final theorem also records the corresponding
pointwise convolution-existence statement.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Pointwise Topology

namespace RegularityStructures.Phi43

private theorem constantsComparison_holder_positive_approxLp {p q : ℝ}
    (h : p.HolderConjugate q) : 0 < p ∧ 0 < q := by
  constructor
  · have hp := Real.holderConjugate_iff.mp h
    linarith [hp.1]
  · have hq := Real.holderConjugate_iff.mp h.symm
    linarith [hq.1]

private theorem constantsComparison_periodise_hasCompactSupport
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (periodise ρ ε) := by
  obtain ⟨a, b, hab⟩ := periodise_eq_zero_outside_time_interval ρ hρ hε
  let K : Set SpaceTime := Icc a b ×ˢ (Set.univ : Set Torus3)
  refine HasCompactSupport.intro (K := K) (isCompact_Icc.prod isCompact_univ) ?_
  intro z hz
  have htime : z.1 ∉ Icc a b := by
    intro hzt
    exact hz ⟨hzt, mem_univ _⟩
  have hleft : z.1 < a ∨ b < z.1 := by
    by_cases h₁ : z.1 < a
    · exact Or.inl h₁
    by_cases h₂ : b < z.1
    · exact Or.inr h₂
    exact False.elim (htime ⟨le_of_not_gt h₁, le_of_not_gt h₂⟩)
  exact hab z hleft

theorem constantsComparison_periodise_memLp
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε) (p : ℝ≥0∞) :
    MemLp (periodise ρ ε) p := by
  obtain ⟨C, hC⟩ := bounded_periodise ρ hρ hε
  let D : ℝ := max C 0
  have hD : 0 ≤ D := le_max_right C 0
  apply (constantsComparison_periodise_hasCompactSupport ρ hρ hε).memLp_of_bound
    (measurable_periodise ρ hρ).aestronglyMeasurable D
  filter_upwards [] with z
  exact (hC z).trans (le_max_left C 0)

theorem constantsComparison_periodise_convolution_exists
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {ε p q : ℝ} (hε : 0 < ε) (hpq : p.HolderConjugate q)
    {f : SpaceTime → ℝ} (hf : MemLp f (ENNReal.ofReal p)) :
    ConvolutionExists (periodise ρ ε) f (ContinuousLinearMap.lsmul ℝ ℝ)
      (volume : Measure SpaceTime) := by
  exact ConvolutionExists.of_memLp_memLp
    (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (μ := (volume : Measure SpaceTime))
    (f := periodise ρ ε) (g := f)
    (p := ENNReal.ofReal q) (q := ENNReal.ofReal p)
    (hpq := hpq.symm.ennrealOfReal)
    (constantsComparison_periodise_memLp ρ hρ hε (ENNReal.ofReal q)) hf

theorem constantsComparison_spaceTimeConvolution_eLpNorm_le
    {k f : SpaceTime → ℝ} {p q : ℝ} (hpq : p.HolderConjugate q)
    (hk : Measurable k) (hki : Integrable k) (hf : Measurable f)
    (hmass : 0 < ∫ y, |k y|)
    (hconv : ∀ᵐ x ∂(volume : Measure SpaceTime),
      Integrable (fun y => k y * f (x - y)))
    (hfp : MemLp f (ENNReal.ofReal p)) :
    eLpNorm (spaceTimeConvolution k f) (ENNReal.ofReal p) ≤
      ENNReal.ofReal (∫ y, |k y|) * eLpNorm f (ENNReal.ofReal p) := by
  obtain ⟨hp, hq⟩ := constantsComparison_holder_positive_approxLp hpq
  have hp0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_pos.mpr hp |>.ne'
  have hptop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hfpow : Integrable (fun x : SpaceTime => |f x| ^ p) := by
    have h := hfp.integrable_norm_rpow hp0 hptop
    simpa [Real.norm_eq_abs, ENNReal.toReal_ofReal hp.le] using h
  obtain ⟨hTpow, _hbound⟩ := constantsComparison_spaceTimeConvolution_integral_rpow_le
    hpq hk hki hf hfpow hconv
  have hTmeas : AEStronglyMeasurable (spaceTimeConvolution k f)
      (volume : Measure SpaceTime) := by
    change AEStronglyMeasurable
      (MeasureTheory.convolution k f (ContinuousLinearMap.lsmul ℝ ℝ) volume)
      (volume : Measure SpaceTime)
    exact hk.aestronglyMeasurable.convolution
      (ContinuousLinearMap.lsmul ℝ ℝ) hf.aestronglyMeasurable
  have hTmem : MemLp (spaceTimeConvolution k f) (ENNReal.ofReal p) := by
    apply (integrable_norm_rpow_iff hTmeas hp0 hptop).mp
    simpa [Real.norm_eq_abs, ENNReal.toReal_ofReal hp.le] using hTpow
  have hbound := constantsComparison_spaceTimeConvolution_integral_rpow_le
    hpq hk hki hf hfpow hconv |>.2
  have hmass0 : 0 ≤ ∫ y, |k y| :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun y => abs_nonneg _)
  have hA0 : 0 ≤ ∫ x, |spaceTimeConvolution k f x| ^ p :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun x =>
      Real.rpow_nonneg (abs_nonneg _) _)
  have hB0 : 0 ≤ ∫ x, |f x| ^ p :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun x =>
      Real.rpow_nonneg (abs_nonneg _) _)
  have hroot :
      (∫ x, |spaceTimeConvolution k f x| ^ p) ^ (1 / p) ≤
        (∫ y, |k y|) * (∫ x, |f x| ^ p) ^ (1 / p) := by
    have hmul : (∫ y, |k y|) ^ (p - 1) * (∫ y, |k y|) =
        (∫ y, |k y|) ^ p := by
      calc
        (∫ y, |k y|) ^ (p - 1) * (∫ y, |k y|) =
            (∫ y, |k y|) ^ (p - 1) * (∫ y, |k y|) ^ (1 : ℝ) := by
              rw [Real.rpow_one]
        _ = (∫ y, |k y|) ^ ((p - 1) + 1) := by
              rw [Real.rpow_add hmass]
        _ = (∫ y, |k y|) ^ p := by ring_nf
    have hbound' : (∫ x, |spaceTimeConvolution k f x| ^ p) ≤
        (∫ y, |k y|) ^ p * (∫ x, |f x| ^ p) := by
      calc
        _ ≤ (∫ y, |k y|) ^ (p - 1) * (∫ y, |k y|) *
            ∫ x, |f x| ^ p := hbound
        _ = _ := by rw [hmul]
    calc
      _ ≤ ((∫ y, |k y|) ^ p * (∫ x, |f x| ^ p)) ^ (1 / p) :=
        Real.rpow_le_rpow hA0 hbound'
          (by simpa [one_div] using (le_of_lt (inv_pos.mpr hp)))
      _ = (∫ y, |k y|) * (∫ x, |f x| ^ p) ^ (1 / p) := by
        rw [Real.mul_rpow (Real.rpow_nonneg hmass0 _) hB0]
        rw [← Real.rpow_mul hmass.le, mul_one_div_cancel hp.ne', Real.rpow_one]
  rw [hTmem.eLpNorm_eq_integral_rpow_norm hp0 hptop,
    hfp.eLpNorm_eq_integral_rpow_norm hp0 hptop]
  simp only [ENNReal.toReal_ofReal hp.le]
  simp only [Real.norm_eq_abs]
  rw [← ENNReal.ofReal_mul hmass0]
  exact ENNReal.ofReal_le_ofReal (by simpa [one_div] using hroot)

private theorem constantsComparison_torusParabolicSize_time_le_sq (z : SpaceTime) :
    |z.1| ≤ torusParabolicSize z ^ 2 := by
  have hs := Real.sq_sqrt (abs_nonneg z.1)
  have hroot : 0 ≤ √|z.1| := Real.sqrt_nonneg _
  have hsp : 0 ≤ torusSpatialNorm z.2 := torusSpatialNorm_nonneg z.2
  unfold torusParabolicSize at hs ⊢
  nlinarith [sq_nonneg (torusSpatialNorm z.2), mul_nonneg hroot hsp]

private theorem constantsComparison_periodise_support_uniform
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) :
    ∃ B : ℝ, 0 < B ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
      Function.support (periodise ρ ε) ⊆
        (Icc (-(B ^ 2)) (B ^ 2) ×ˢ (Set.univ : Set Torus3)) := by
  obtain ⟨B, hB, hsupport⟩ := periodise_support_parabolic_bound ρ hρ
  refine ⟨B, hB, ?_⟩
  intro ε hε hε1 z hz
  have hz' : periodise ρ ε z ≠ 0 := by
    simpa only [Function.mem_support] using hz
  have hs := hsupport hε hε1 z hz'
  have hBε : B * ε ≤ B := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hε1 hB.le
  have hsize : torusParabolicSize z ≤ B := hs.trans hBε
  have htime : |z.1| ≤ B ^ 2 := by
    calc
      |z.1| ≤ torusParabolicSize z ^ 2 :=
        constantsComparison_torusParabolicSize_time_le_sq z
      _ ≤ B ^ 2 := by
        exact sq_le_sq₀ (torusParabolicSize_nonneg z) hB.le |>.2 hsize
  have htime' := abs_le.mp htime
  exact ⟨⟨htime'.1, htime'.2⟩, mem_univ _⟩

private theorem constantsComparison_periodise_convolution_integral_rpow_tendsto_of_continuous_compactSupport
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    (g : SpaceTime → ℝ) (hg : Continuous g) (hgs : HasCompactSupport g)
    {p : ℝ} (hp : 0 < p) :
    Tendsto
      (fun ε : ℝ => ∫ x,
        |spaceTimeConvolution (periodise ρ ε) g x - g x| ^ p)
      (𝓝[>] 0) (𝓝 0) := by
  let B : ℝ := ∫ y : ParabolicSpace, |ρ y|
  have hB : 0 ≤ B := by
    dsimp [B]
    exact integral_nonneg_of_ae (Eventually.of_forall fun y => abs_nonneg _)
  have hmass : ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
      ∫ y : SpaceTime, |periodise ρ ε y| ≤ B := by
    intro ε hε hε1
    dsimp [B]
    calc
      ∫ y : SpaceTime, |periodise ρ ε y| ≤ ∫ y : ParabolicSpace, |rescale ρ ε y| :=
        integral_abs_periodise_le ρ hρ hε hε1
      _ = ∫ y : ParabolicSpace, |ρ y| := integral_abs_rescale_eq ρ hε
  let l : Filter ℝ := 𝓝[>] 0
  have hpos : ∀ᶠ ε in l, 0 < ε := self_mem_nhdsWithin
  have hle : ∀ᶠ ε in l, ε ≤ 1 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num))
  have hgmem : MemLp g (ENNReal.ofReal p) := hg.memLp_of_hasCompactSupport hgs
  have hgp0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_pos.mpr hp |>.ne'
  have hgptop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hM : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖g x‖ ≤ M := by
    obtain ⟨C, hC⟩ := hgs.isCompact.bddAbove_image hg.norm.continuousOn
    refine ⟨max C 0, le_max_right C 0, ?_⟩
    intro x
    by_cases hx : x ∈ tsupport g
    · exact (hC (mem_image_of_mem (fun y => ‖g y‖) hx)).trans (le_max_left C 0)
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  obtain ⟨M, hM0, hMbound⟩ := hM
  let D : ℝ := ((B + 1) * (M + 1)) ^ p
  have hD : 0 ≤ D := by positivity
  obtain ⟨C, _hC, _hCsupport⟩ := constantsComparison_periodise_support_uniform ρ hρ
  let K : Set SpaceTime :=
    (tsupport g + (Icc (-(C ^ 2)) (C ^ 2) ×ˢ (Set.univ : Set Torus3))) ∪ tsupport g
  have hKcompact : IsCompact K := by
    dsimp [K]
    exact (hgs.isCompact.add (isCompact_Icc.prod isCompact_univ)).union hgs.isCompact
  have hdom : Integrable (K.indicator (fun _ : SpaceTime => D)) := by
    exact ((integrableOn_const (s := K) (hs := hKcompact.measure_ne_top) :
      IntegrableOn (fun _ : SpaceTime => D) K volume).integrable_indicator
        hKcompact.measurableSet)
  have hpoint : ∀ x : SpaceTime, Tendsto
      (fun ε : ℝ =>
        |spaceTimeConvolution (periodise ρ ε) g x - g x| ^ p)
      l (𝓝 0) := by
    intro x
    have hxconv := constantsComparison_periodise_convolution_tendsto_of_continuous_compactSupport
      ρ hρ g hg hgs x
    have hxsub : Tendsto
        (fun ε : ℝ => spaceTimeConvolution (periodise ρ ε) g x - g x)
        l (𝓝 0) := by
      simpa [l] using hxconv.sub
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => g x) (𝓝[>] 0) (𝓝 (g x)))
    have hxabs : Tendsto
        (fun ε : ℝ => |spaceTimeConvolution (periodise ρ ε) g x - g x|)
        l (𝓝 0) := by
      simpa [Function.comp_def, Real.norm_eq_abs] using
        (continuous_norm.continuousAt.tendsto.comp hxsub)
    simpa [Function.comp_def, Real.zero_rpow hp.ne'] using
      (Real.continuousAt_rpow_const (0 : ℝ) p (Or.inr hp.le)).tendsto.comp hxabs
  have hbound : ∀ᶠ ε in l, ∀ᵐ x : SpaceTime,
      |spaceTimeConvolution (periodise ρ ε) g x - g x| ^ p ≤
        (K.indicator (fun _ : SpaceTime => D)) x := by
    filter_upwards [hpos, hle] with ε hε hε1
    filter_upwards [] with x
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx]
      have hpointwise : |spaceTimeConvolution (periodise ρ ε) g x| ≤ B * M := by
        have hi := norm_integral_le_integral_norm
          (μ := (volume : Measure SpaceTime))
          (f := fun y : SpaceTime => periodise ρ ε y * g (x - y))
        calc
          |spaceTimeConvolution (periodise ρ ε) g x| ≤
              ∫ y, |periodise ρ ε y * g (x - y)| := by
            simpa [spaceTimeConvolution, Real.norm_eq_abs] using hi
          _ ≤ ∫ y, M * |periodise ρ ε y| := by
            apply integral_mono_of_nonneg
              (Eventually.of_forall fun y => abs_nonneg _)
              ((integrable_periodise ρ hρ hε).norm.const_mul M)
              (Filter.Eventually.of_forall fun y => by
                calc
                  ‖periodise ρ ε y * g (x - y)‖ =
                      |periodise ρ ε y| * |g (x - y)| := by
                    simp only [Real.norm_eq_abs, abs_mul]
                  _ ≤ |periodise ρ ε y| * M :=
                    mul_le_mul_of_nonneg_left (hMbound (x - y))
                      (abs_nonneg _)
                  _ = M * ‖periodise ρ ε y‖ := by
                    simp only [Real.norm_eq_abs]
                    ring)
          _ = M * ∫ y, |periodise ρ ε y| := by rw [integral_const_mul]
          _ ≤ M * B := mul_le_mul_of_nonneg_left (hmass hε hε1) hM0
          _ = B * M := by ring
      have hdiff : |spaceTimeConvolution (periodise ρ ε) g x - g x| ≤ B * M + M := by
        calc
          _ ≤ |spaceTimeConvolution (periodise ρ ε) g x| + |g x| := by
            simpa using (abs_sub_le (spaceTimeConvolution (periodise ρ ε) g x) 0 (g x))
          _ ≤ B * M + M := add_le_add hpointwise (hMbound x)
      exact (Real.rpow_le_rpow (abs_nonneg _) hdiff (le_of_lt hp)).trans (by
        have hbase : B * M + M ≤ (B + 1) * (M + 1) := by nlinarith
        dsimp [D]
        exact Real.rpow_le_rpow (by positivity) hbase (le_of_lt hp))
    · have hKsub : Function.support
          (fun x => spaceTimeConvolution (periodise ρ ε) g x - g x) ⊆ K := by
        intro y hy
        have hconvsub : Function.support (spaceTimeConvolution (periodise ρ ε) g) ⊆
            tsupport g + (Icc (-(C ^ 2)) (C ^ 2) ×ˢ (Set.univ : Set Torus3)) := by
          exact (MeasureTheory.support_convolution_subset_swap
            (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := (volume : Measure SpaceTime))).trans
            (add_subset_add subset_closure (_hCsupport hε hε1))
        by_cases hT : spaceTimeConvolution (periodise ρ ε) g y = 0
        · have hg' : g y ≠ 0 := by
            intro hg'
            apply hy
            simp [hT, hg']
          exact Or.inr (subset_closure (by
            simpa only [Function.mem_support] using hg'))
        · exact Or.inl (hconvsub (by simpa only [Function.mem_support] using hT))
      have hzero : spaceTimeConvolution (periodise ρ ε) g x - g x = 0 := by
        by_contra hne
        exact hx (hKsub (by simpa only [Function.mem_support] using hne))
      simp [hzero, Set.indicator_of_notMem hx, hp.ne']
  have hIntegral : Tendsto
      (fun ε : ℝ => ∫ x, |spaceTimeConvolution (periodise ρ ε) g x - g x| ^ p)
      l (𝓝 0) := by
    let μ : Measure SpaceTime := volume
    have hFmeas : ∀ᶠ ε in l, AEStronglyMeasurable
        (fun x => ‖spaceTimeConvolution (periodise ρ ε) g x - g x‖ ^ p)
        μ := by
      filter_upwards [hpos] with ε hε
      have hconvmeas : AEStronglyMeasurable
          (spaceTimeConvolution (periodise ρ ε) g)
          μ := by
        change AEStronglyMeasurable
          (MeasureTheory.convolution (periodise ρ ε) g
            (ContinuousLinearMap.lsmul ℝ ℝ) volume) μ
        exact (measurable_periodise ρ hρ).aestronglyMeasurable.convolution
          (ContinuousLinearMap.lsmul ℝ ℝ) hg.aestronglyMeasurable
      have hpow := ((hconvmeas.sub hg.aestronglyMeasurable).norm.aemeasurable.pow_const p).aestronglyMeasurable
      change AEStronglyMeasurable
        (fun x => |spaceTimeConvolution (periodise ρ ε) g x - g x| ^ p) μ
      simpa only [Pi.sub_apply, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] using hpow
    have hpoint' : ∀ x : SpaceTime, Tendsto
        (fun ε : ℝ => ‖spaceTimeConvolution (periodise ρ ε) g x - g x‖ ^ p)
        l (𝓝 0) := by
      intro x
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] using hpoint x
    have hDCT : Tendsto
        (fun ε : ℝ => ∫ x, ‖spaceTimeConvolution (periodise ρ ε) g x - g x‖ ^ p ∂μ)
        l (𝓝 (∫ _ : SpaceTime, (0 : ℝ) ∂μ)) := by
      refine tendsto_integral_filter_of_dominated_convergence
        (μ := μ) (K.indicator (fun _ : SpaceTime => D)) hFmeas ?_ (by
          simpa [μ] using hdom)
        (Filter.Eventually.of_forall hpoint')
      filter_upwards [hbound] with ε hε
      filter_upwards [hε] with x hx
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] using hx
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), integral_zero, μ] using hDCT
  exact hIntegral

private theorem constantsComparison_periodise_convolution_sub_eLpNorm_eq
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε)
    (g : SpaceTime → ℝ) (hg : Continuous g) (hgs : HasCompactSupport g)
    {p : ℝ} (hp : 1 < p) :
    eLpNorm
        (fun x => spaceTimeConvolution (periodise ρ ε) g x - g x)
        (ENNReal.ofReal p) =
      ENNReal.ofReal ((∫ x, |spaceTimeConvolution (periodise ρ ε) g x - g x| ^ p) ^
        (1 / p)) := by
  have hgmem : MemLp g (ENNReal.ofReal p) := hg.memLp_of_hasCompactSupport hgs
  have hgp0 : ENNReal.ofReal p ≠ 0 :=
    ENNReal.ofReal_pos.mpr (lt_trans zero_lt_one hp) |>.ne'
  have hgptop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  let q : ℝ := p / (p - 1)
  have hpq : p.HolderConjugate q := by
    dsimp [q]
    exact Real.HolderConjugate.conjExponent hp
  have hconv := constantsComparison_periodise_convolution_exists ρ hρ hε hpq hgmem
  have hTmem : MemLp (spaceTimeConvolution (periodise ρ ε) g) (ENNReal.ofReal p) := by
    have hmass : 0 < ∫ y : SpaceTime, |periodise ρ ε y| := by
      have habs := abs_integral_le_integral_abs (f := periodise ρ ε)
        (μ := (volume : Measure SpaceTime))
      rw [constantsComparison_periodise_mass ρ hρ hε] at habs
      exact lt_of_lt_of_le zero_lt_one (by simpa using habs)
    have hconv_ae : ∀ᵐ x : SpaceTime,
        Integrable (fun y => periodise ρ ε y * g (x - y)) :=
      Filter.Eventually.of_forall (fun x => hconv x)
    have hTbound := constantsComparison_spaceTimeConvolution_eLpNorm_le
      (k := periodise ρ ε) (f := g) (p := p) (q := q)
      hpq (measurable_periodise ρ hρ)
      (integrable_periodise ρ hρ hε) hg.measurable hmass hconv_ae hgmem
    exact (memLp_iff.mpr (lt_of_le_of_lt hTbound (by finiteness)))
  have hdiffmem : MemLp (fun x => spaceTimeConvolution (periodise ρ ε) g x - g x)
      (ENNReal.ofReal p) := hTmem.sub hgmem
  have hp0 : 0 ≤ p := le_trans zero_le_one hp.le
  rw [hdiffmem.eLpNorm_eq_integral_rpow_norm hgp0 hgptop]
  simp [ENNReal.toReal_ofReal hp0, Real.norm_eq_abs, one_div]

private theorem constantsComparison_periodise_convolution_sub_rpowRoot_tendsto
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    (g : SpaceTime → ℝ) (hg : Continuous g) (hgs : HasCompactSupport g)
    {p : ℝ} (hp : 0 < p) :
    Tendsto
      (fun ε : ℝ =>
        (∫ x, |spaceTimeConvolution (periodise ρ ε) g x - g x| ^ p) ^ (1 / p))
      (𝓝[>] 0) (𝓝 0) := by
  have hIntegral :=
    constantsComparison_periodise_convolution_integral_rpow_tendsto_of_continuous_compactSupport
      ρ hρ g hg hgs hp
  have hpinv : (1 / p : ℝ) ≠ 0 := by positivity
  have hpinv' : p⁻¹ ≠ 0 := inv_ne_zero hp.ne'
  have hcomp :=
    (Real.continuous_rpow_const (by positivity : 0 ≤ (1 / p : ℝ))).tendsto 0 |>.comp
      hIntegral
  simpa [Function.comp_def, one_div, Real.zero_rpow hpinv'] using hcomp

private theorem constantsComparison_tendsto_of_eventuallyEq
    {α β : Type*} [TopologicalSpace β]
    {l : Filter α} {f g : α → β} {b : β}
    (hg : Tendsto g l (𝓝 b)) (hfg : ∀ᶠ x in l, f x = g x) :
    Tendsto f l (𝓝 b) := by
  apply hg.congr'
  filter_upwards [hfg] with x hx
  exact hx.symm

theorem constantsComparison_periodise_convolution_eLpNorm_tendsto_of_continuous_compactSupport
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    (g : SpaceTime → ℝ) (hg : Continuous g) (hgs : HasCompactSupport g)
    {p : ℝ} (hp : 1 < p) :
    Tendsto
      (fun ε : ℝ =>
        eLpNorm
          (fun x => spaceTimeConvolution (periodise ρ ε) g x - g x)
          (ENNReal.ofReal p))
      (𝓝[>] 0) (𝓝 0) := by
  let l : Filter ℝ := 𝓝[>] 0
  have hpos : ∀ᶠ ε in l, 0 < ε := self_mem_nhdsWithin
  have hle : ∀ᶠ ε in l, ε ≤ 1 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num))
  have hroot :=
    constantsComparison_periodise_convolution_sub_rpowRoot_tendsto
      ρ hρ g hg hgs (lt_trans zero_lt_one hp)
  have hrootENN : Tendsto
      (fun ε : ℝ => ENNReal.ofReal
        ((∫ x, |spaceTimeConvolution (periodise ρ ε) g x - g x| ^ p) ^ (1 / p)))
      l (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, l, Function.comp_def] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hroot
  have hEq : ∀ᶠ ε in l,
      eLpNorm
          (fun x => spaceTimeConvolution (periodise ρ ε) g x - g x)
          (ENNReal.ofReal p) = ENNReal.ofReal
        ((∫ x, |spaceTimeConvolution (periodise ρ ε) g x - g x| ^ p) ^ (1 / p)) := by
    filter_upwards [hpos, hle] with ε hε _hε1
    exact constantsComparison_periodise_convolution_sub_eLpNorm_eq ρ hρ hε g hg hgs hp
  exact constantsComparison_tendsto_of_eventuallyEq hrootENN hEq

private theorem constantsComparison_periodise_convolution_sub_eLpNorm_eq_one
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε)
    (g : SpaceTime → ℝ) (hg : Continuous g) (hgs : HasCompactSupport g) :
    eLpNorm
        (fun x => spaceTimeConvolution (periodise ρ ε) g x - g x) 1 =
      ENNReal.ofReal (∫ x, |spaceTimeConvolution (periodise ρ ε) g x - g x|) := by
  have hgmem : MemLp g 1 := hg.memLp_of_hasCompactSupport hgs
  have hgint : Integrable g := memLp_one_iff_integrable.mp hgmem
  have hconvint : Integrable (spaceTimeConvolution (periodise ρ ε) g) := by
    change Integrable
      (MeasureTheory.convolution (periodise ρ ε) g
        (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure SpaceTime))
    exact (integrable_periodise ρ hρ hε).integrable_convolution
      (ContinuousLinearMap.lsmul ℝ ℝ) hgint
  have hTmem : MemLp (spaceTimeConvolution (periodise ρ ε) g) 1 :=
    memLp_one_iff_integrable.mpr hconvint
  have hdiffmem : MemLp (fun x => spaceTimeConvolution (periodise ρ ε) g x - g x) 1 :=
    hTmem.sub hgmem
  rw [hdiffmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp)]
  simp [Real.norm_eq_abs]

theorem constantsComparison_periodise_convolution_eLpNorm_tendsto_of_continuous_compactSupport_one
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    (g : SpaceTime → ℝ) (hg : Continuous g) (hgs : HasCompactSupport g) :
    Tendsto
      (fun ε : ℝ =>
        eLpNorm
          (fun x => spaceTimeConvolution (periodise ρ ε) g x - g x) 1)
      (𝓝[>] 0) (𝓝 0) := by
  let l : Filter ℝ := 𝓝[>] 0
  have hpos : ∀ᶠ ε in l, 0 < ε := self_mem_nhdsWithin
  have hroot :=
    constantsComparison_periodise_convolution_integral_rpow_tendsto_of_continuous_compactSupport
      ρ hρ g hg hgs zero_lt_one
  have hrootENN : Tendsto
      (fun ε : ℝ => ENNReal.ofReal
        (∫ x, |spaceTimeConvolution (periodise ρ ε) g x - g x|))
      l (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, l, Function.comp_def, Real.rpow_one] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hroot
  have hEq : ∀ᶠ ε in l,
      eLpNorm
          (fun x => spaceTimeConvolution (periodise ρ ε) g x - g x) 1 =
        ENNReal.ofReal (∫ x, |spaceTimeConvolution (periodise ρ ε) g x - g x|) := by
    filter_upwards [hpos] with ε hε
    exact constantsComparison_periodise_convolution_sub_eLpNorm_eq_one ρ hρ hε g hg hgs
  exact constantsComparison_tendsto_of_eventuallyEq hrootENN hEq

theorem constantsComparison_periodise_convolution_eLpNorm_tendsto_of_continuous_compactSupport_of_one_le
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    (g : SpaceTime → ℝ) (hg : Continuous g) (hgs : HasCompactSupport g)
    {p : ℝ} (hp : 1 ≤ p) :
    Tendsto
      (fun ε : ℝ =>
        eLpNorm
          (fun x => spaceTimeConvolution (periodise ρ ε) g x - g x)
          (ENNReal.ofReal p))
      (𝓝[>] 0) (𝓝 0) := by
  rcases eq_or_lt_of_le hp with rfl | hp
  · simpa only [ENNReal.ofReal_one] using
      (constantsComparison_periodise_convolution_eLpNorm_tendsto_of_continuous_compactSupport_one
        ρ hρ g hg hgs)
  · exact constantsComparison_periodise_convolution_eLpNorm_tendsto_of_continuous_compactSupport
      ρ hρ g hg hgs hp

end RegularityStructures.Phi43

end
