/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsComparisonApproxLpGeneral
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import RegularityStructures.Probability.AnnealedNoiseBridge

/-!
# Convergence of the conjugate-exponent pairings

The covariance comparison and the causal time-cut argument use the continuous `L⁴ × L^(4/3)`
pairing. This module converts convergence in the function seminorms to convergence of the actual
Bochner integrals. Membership of the regularised functions is only needed eventually.
-/

public noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace RegularityStructures.Phi43

private def comparisonPairing_LpOf
    {p : ℝ≥0∞} {f : SpaceTime → ℝ} (hf : MemLp f p)
    (g : SpaceTime → ℝ) : Lp ℝ p (volume : Measure SpaceTime) := by
  classical
  exact if h : MemLp g p then h.toLp g else hf.toLp f

private theorem comparisonPairing_toLp_tendsto
    {ι : Type*} {l : Filter ι} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {f : SpaceTime → ℝ} (hf : MemLp f p)
    {fs : ι → SpaceTime → ℝ} (hfs : ∀ᶠ i in l, MemLp (fs i) p)
    (hlim : Tendsto (fun i => eLpNorm (fs i - f) p) l (𝓝 0)) :
    Tendsto (fun i => comparisonPairing_LpOf hf (fs i))
      l (𝓝 (hf.toLp f)) := by
  classical
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hr := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
  apply hr.congr'
  filter_upwards [hfs] with i hi
  simp only [comparisonPairing_LpOf, dite_eq_left hi, Lp.dist_edist,
    Lp.edist_toLp_toLp, Function.comp_apply]

/-- Continuity of the actual Hölder pairing, from eventual membership and seminorm convergence. -/
theorem constantsComparison_pairing_tendsto_of_eLpNorm
    {ι : Type*} {l : Filter ι} {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    {f g : SpaceTime → ℝ} (hf : MemLp f p) (hg : MemLp g q)
    {fs gs : ι → SpaceTime → ℝ}
    (hfs : ∀ᶠ i in l, MemLp (fs i) p) (hgs : ∀ᶠ i in l, MemLp (gs i) q)
    (hflim : Tendsto (fun i => eLpNorm (fs i - f) p) l (𝓝 0))
    (hglim : Tendsto (fun i => eLpNorm (gs i - g) q) l (𝓝 0)) :
    Tendsto (fun i => ∫ z, fs i z * gs i z) l (𝓝 (∫ z, f z * g z)) := by
  classical
  let F : ι → Lp ℝ p (volume : Measure SpaceTime) :=
    fun i => comparisonPairing_LpOf hf (fs i)
  let G : ι → Lp ℝ q (volume : Measure SpaceTime) :=
    fun i => comparisonPairing_LpOf hg (gs i)
  have hF : Tendsto F l (𝓝 (hf.toLp f)) := comparisonPairing_toLp_tendsto hf hfs hflim
  have hG : Tendsto G l (𝓝 (hg.toLp g)) := comparisonPairing_toLp_tendsto hg hgs hglim
  let B := (ContinuousLinearMap.mul ℝ ℝ).lpPairing (volume : Measure SpaceTime) p q
  have hb := B.continuous₂.tendsto (hf.toLp f, hg.toLp g)
  have hresult := hb.comp (hF.prodMk_nhds hG)
  change Tendsto (fun i => B (F i) (G i)) l
    (𝓝 (B (hf.toLp f) (hg.toLp g))) at hresult
  have hbase : B (hf.toLp f) (hg.toLp g) = ∫ z, f z * g z := by
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with z hfz hgz
    simp only [ContinuousLinearMap.mul_apply', hfz, hgz]
  rw [hbase] at hresult
  apply hresult.congr'
  filter_upwards [hfs, hgs] with i hfi hgi
  dsimp only [F, G]
  simp only [comparisonPairing_LpOf, dite_eq_left hfi, dite_eq_left hgi]
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [hfi.coeFn_toLp, hgi.coeFn_toLp] with z hfz hgz
  simp only [ContinuousLinearMap.mul_apply', hfz, hgz]

/-- Signed mollification preserves every finite exponent greater than one. -/
theorem constantsComparison_mollification_memLp
    (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ)
    {ε p q : ℝ} (hε : 0 < ε) (hpq : p.HolderConjugate q)
    {f : SpaceTime → ℝ} (hf : MemLp f (ENNReal.ofReal p)) (hfm : Measurable f) :
    MemLp (spaceTimeConvolution (periodise ρ ε) f) (ENNReal.ofReal p) := by
  have hmass : 0 < ∫ y : SpaceTime, |periodise ρ ε y| := by
    have habs := abs_integral_le_integral_abs (f := periodise ρ ε)
      (μ := (volume : Measure SpaceTime))
    rw [constantsComparison_periodise_mass ρ hρ hε] at habs
    exact lt_of_lt_of_le zero_lt_one (by simpa using habs)
  have hconv := constantsComparison_periodise_convolution_exists ρ hρ hε hpq hf
  have hbound := constantsComparison_spaceTimeConvolution_eLpNorm_le hpq
    (measurable_periodise ρ hρ) (integrable_periodise ρ hρ hε) hfm hmass
    (Eventually.of_forall fun x => hconv x) hf
  exact memLp_iff.mpr (lt_of_le_of_lt hbound (by finiteness))

/-- Mollification converges in every translated `L⁴ × L^(4/3)` covariance pairing. -/
theorem constantsComparison_mollifiedPairing_tendsto
    (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ)
    {f g : SpaceTime → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : MemLp f (ENNReal.ofReal 4)) (hg : MemLp g (ENNReal.ofReal (4 / 3 : ℝ)))
    (z : SpaceTime) :
    Tendsto (fun ε : ℝ => ∫ w,
      spaceTimeConvolution (periodise ρ ε) f (z + w) *
        spaceTimeConvolution (periodise ρ ε) g w)
      (𝓝[>] 0) (𝓝 (∫ w, f (z + w) * g w)) := by
  have hpq : (4 : ℝ).HolderConjugate (4 / 3 : ℝ) := by
    apply Real.holderConjugate_iff.mpr
    constructor <;> norm_num
  have : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal 4) := ⟨by norm_num⟩
  have : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal (4 / 3 : ℝ)) := ⟨by norm_num⟩
  have : (ENNReal.ofReal 4).HolderConjugate (ENNReal.ofReal (4 / 3 : ℝ)) :=
    hpq.ennrealOfReal
  have hshift : MeasurePreserving (fun w : SpaceTime => z + w) volume volume :=
    measurePreserving_add_left volume z
  apply constantsComparison_pairing_tendsto_of_eLpNorm
    (hf.comp_measurePreserving hshift) hg
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (constantsComparison_mollification_memLp ρ hρ hε hpq hf hfm).comp_measurePreserving
      hshift
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact constantsComparison_mollification_memLp ρ hρ hε hpq.symm hg hgm
  · have hlim := constantsComparison_periodise_convolution_eLpNorm_tendsto_of_memLp
      ρ hρ f hfm (by norm_num : (1 : ℝ) < 4) hf
    apply hlim.congr'
    filter_upwards [] with ε
    exact (eLpNorm_comp_measurePreserving
      (((measurable_periodise ρ hρ).aestronglyMeasurable.convolution
        (ContinuousLinearMap.lsmul ℝ ℝ) hfm.aestronglyMeasurable).sub
          hf.aestronglyMeasurable) hshift).symm
  · exact constantsComparison_periodise_convolution_eLpNorm_tendsto_of_memLp
      ρ hρ g hgm (by norm_num : (1 : ℝ) < 4 / 3) hg

/-- Translation swaps the two factors of a covariance pairing. -/
theorem constantsComparison_correlation_swap (f g : SpaceTime → ℝ) (z : SpaceTime) :
    (∫ w, f (z + w) * g w) = ∫ w, g (-z + w) * f w := by
  have h := integral_comp_add_left_spaceTime (fun w => g (-z + w) * f w) z
  simpa only [neg_add_cancel_left, mul_comm] using h

/-- The reversed conjugate-exponent pairing. -/
theorem constantsComparison_mollifiedPairing_tendsto_reverse
    (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ)
    {f g : SpaceTime → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : MemLp f (ENNReal.ofReal (4 / 3 : ℝ))) (hg : MemLp g (ENNReal.ofReal 4))
    (z : SpaceTime) :
    Tendsto (fun ε : ℝ => ∫ w,
      spaceTimeConvolution (periodise ρ ε) f (z + w) *
        spaceTimeConvolution (periodise ρ ε) g w)
      (𝓝[>] 0) (𝓝 (∫ w, f (z + w) * g w)) := by
  have h := constantsComparison_mollifiedPairing_tendsto ρ hρ hgm hfm hg hf (-z)
  rw [← constantsComparison_correlation_swap f g z] at h
  apply h.congr'
  filter_upwards [] with ε
  exact (constantsComparison_correlation_swap
    (spaceTimeConvolution (periodise ρ ε) f)
    (spaceTimeConvolution (periodise ρ ε) g) z).symm

end RegularityStructures.Phi43

end
