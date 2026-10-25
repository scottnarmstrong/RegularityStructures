/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsComparisonApproxLp
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import RegularityStructures.Probability.AnnealedNoiseBridge

/-!
# The signed approximate identity on finite `Lᵖ`

The compact-support result is extended by the standard density argument.  The proof keeps the
kernel signed: the only uniform input is the total-variation bound supplied by the periodised
mollifier.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace RegularityStructures.Phi43

private theorem constantsComparison_eLpNorm_sub_add_le
    {A B C : SpaceTime → ℝ} {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (A + B - C) p ≤
      eLpNorm A p + eLpNorm B p + eLpNorm C p :=
  (eLpNorm_sub_le hp).trans (add_le_add_left (eLpNorm_add_le hp) _)

theorem constantsComparison_periodise_convolution_eLpNorm_tendsto_of_memLp
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    (f : SpaceTime → ℝ) (hf : Measurable f)
    {p : ℝ} (hp : 1 < p) (hfp : MemLp f (ENNReal.ofReal p)) :
    Tendsto
      (fun ε : ℝ =>
        eLpNorm
          (fun x => spaceTimeConvolution (periodise ρ ε) f x - f x)
          (ENNReal.ofReal p))
      (𝓝[>] 0) (𝓝 0) := by
  let l : Filter ℝ := 𝓝[>] 0
  let Kreg : Set SpaceTime := Icc (-(1 : ℝ)) 1 ×ˢ (Set.univ : Set Torus3)
  have hKreg : IsCompact Kreg := by
    dsimp [Kreg]
    exact isCompact_Icc.prod isCompact_univ
  have hKreg_nhds : Kreg ∈ 𝓝 (0 : SpaceTime) := by
    have hopen : IsOpen (Ioo (-(1 : ℝ)) 1 ×ˢ (Set.univ : Set Torus3)) :=
      isOpen_Ioo.prod isOpen_univ
    have hsub : Ioo (-(1 : ℝ)) 1 ×ˢ (Set.univ : Set Torus3) ⊆ Kreg := by
      intro z hz
      exact ⟨⟨le_of_lt hz.1.1, le_of_lt hz.1.2⟩, mem_univ _⟩
    exact Filter.mem_of_superset (hopen.mem_nhds ⟨by norm_num, mem_univ _⟩) hsub
  let hregular : (volume : Measure SpaceTime).Regular :=
    Measure.regular_of_isAddLeftInvariant hKreg
      ⟨0, mem_interior_iff_mem_nhds.mpr hKreg_nhds⟩
      (IsFiniteMeasureOnCompacts.lt_top_of_isCompact hKreg).ne
  have hp0 : 0 ≤ p := le_trans zero_le_one hp.le
  have hpenn : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using
      ENNReal.ofReal_le_ofReal hp.le
  have hpne : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  let B : ℝ := ∫ y : ParabolicSpace, |ρ y|
  have hB : 0 ≤ B := by
    dsimp [B]
    exact integral_nonneg_of_ae (Eventually.of_forall fun y => abs_nonneg _)
  have hB_one : 1 ≤ B := by
    have habs := abs_integral_le_integral_abs (f := ρ)
      (μ := (volume : Measure ParabolicSpace))
    rw [hρ.integral_eq_one] at habs
    simpa [B] using habs
  let Benn : ℝ≥0∞ := ENNReal.ofReal B
  have hBennone : 1 ≤ Benn := by
    dsimp [Benn]
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hB_one
  have hBennzero : Benn ≠ 0 := (zero_lt_one.trans_le hBennone).ne'
  have hBenntop : Benn ≠ ∞ := ENNReal.ofReal_ne_top
  let q : ℝ := p / (p - 1)
  have hpq : p.HolderConjugate q := by
    dsimp [q]
    exact Real.HolderConjugate.conjExponent hp
  have hmass : ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
      0 < ∫ y : SpaceTime, |periodise ρ ε y| ∧
      ∫ y : SpaceTime, |periodise ρ ε y| ≤ B := by
    intro ε hε hε1
    constructor
    · have habs := abs_integral_le_integral_abs (f := periodise ρ ε)
        (μ := (volume : Measure SpaceTime))
      rw [constantsComparison_periodise_mass ρ hρ hε] at habs
      exact lt_of_lt_of_le zero_lt_one (by simpa using habs)
    · dsimp [B]
      calc
        ∫ y : SpaceTime, |periodise ρ ε y| ≤ ∫ y : ParabolicSpace, |rescale ρ ε y| :=
          integral_abs_periodise_le ρ hρ hε hε1
        _ = ∫ y : ParabolicSpace, |ρ y| := integral_abs_rescale_eq ρ hε
  refine ENNReal.tendsto_nhds_zero.2 ?_
  intro a ha
  have hwork : ∀ᶠ ε in l,
      eLpNorm
          (fun x => spaceTimeConvolution (periodise ρ ε) f x - f x)
          (ENNReal.ofReal p) ≤ a := by
    let η : ℝ≥0∞ := (a / 4) / Benn
    have hηpos : 0 < η := by
      dsimp [η]
      have ha4 : a / 4 ≠ 0 := ENNReal.div_ne_zero.mpr ⟨ha.ne', by norm_num⟩
      exact ENNReal.div_pos ha4 hBenntop
    have hηne : η ≠ 0 := hηpos.ne'
    obtain ⟨g, hgSupport, hfg, hg, hgmem⟩ :=
      @MemLp.exists_hasCompactSupport_eLpNorm_sub_le SpaceTime _ _ _ _ ℝ _
        (volume : Measure SpaceTime) (ENNReal.ofReal p) _ _ _ hregular hpne f hfp η hηne
    have hηle : η ≤ a / 4 := by
      dsimp [η]
      apply (ENNReal.div_le_iff' hBennzero hBenntop).2
      calc
        a / 4 = 1 * (a / 4) := by rw [one_mul]
        _ ≤ Benn * (a / 4) := by gcongr
    have hcompact :=
      constantsComparison_periodise_convolution_eLpNorm_tendsto_of_continuous_compactSupport_of_one_le
        ρ hρ g hg hgSupport hp.le
    have hcompact_event : ∀ᶠ ε in l,
        eLpNorm
            (fun x => spaceTimeConvolution (periodise ρ ε) g x - g x)
            (ENNReal.ofReal p) ≤ a / 4 := by
      simpa [l] using (ENNReal.tendsto_nhds_zero.1 hcompact) (a / 4)
        (ENNReal.div_pos ha.ne' (by norm_num))
    have hpos : ∀ᶠ ε in l, 0 < ε := self_mem_nhdsWithin
    have hle : ∀ᶠ ε in l, ε ≤ 1 :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num))
    have hsmall : ∀ᶠ ε in l,
        eLpNorm
            (fun x => spaceTimeConvolution (periodise ρ ε) (fun y => f y - g y) x)
            (ENNReal.ofReal p) ≤ a / 4 := by
      filter_upwards [hpos, hle] with ε hε hε1
      have hdiffmem : MemLp (fun y => f y - g y) (ENNReal.ofReal p) := hfp.sub hgmem
      have hconv := constantsComparison_periodise_convolution_exists ρ hρ hε hpq hdiffmem
      have hconv_ae : ∀ᵐ x : SpaceTime,
          Integrable (fun y => periodise ρ ε y * (f (x - y) - g (x - y))) :=
        Eventually.of_forall (fun x => hconv x)
      have hmass' := hmass hε hε1
      have hOp := constantsComparison_spaceTimeConvolution_eLpNorm_le
        (k := periodise ρ ε) (f := fun y => f y - g y)
        (p := p) (q := q) hpq
        (measurable_periodise ρ hρ) (integrable_periodise ρ hρ hε)
        (hf.sub hg.measurable) hmass'.1 hconv_ae hdiffmem
      have hBη : Benn * η = a / 4 := by
        dsimp [η]
        rw [mul_comm, ENNReal.div_mul_cancel hBennzero hBenntop]
      refine hOp.trans (le_of_le_of_eq ?_ hBη)
      gcongr
      · exact ENNReal.ofReal_le_ofReal hmass'.2
      · exact hfg
    have hfull : ∀ᶠ ε in l,
        eLpNorm
            (fun x => spaceTimeConvolution (periodise ρ ε) f x - f x)
            (ENNReal.ofReal p) ≤ a := by
      filter_upwards [hsmall, hcompact_event, hpos, hle] with ε hsmallε hcompactε hε hε1
      have hdiffmem : MemLp (fun y => f y - g y) (ENNReal.ofReal p) := hfp.sub hgmem
      have hconvF := constantsComparison_periodise_convolution_exists ρ hρ hε hpq hfp
      have hconvG := constantsComparison_periodise_convolution_exists ρ hρ hε hpq hgmem
      have hconvD := constantsComparison_periodise_convolution_exists ρ hρ hε hpq hdiffmem
      have hlin : spaceTimeConvolution (periodise ρ ε) f =
          spaceTimeConvolution (periodise ρ ε) (fun y => f y - g y) +
            spaceTimeConvolution (periodise ρ ε) g := by
        have hadd := hconvD.distrib_add hconvG
        calc
          MeasureTheory.convolution (periodise ρ ε) f
              (ContinuousLinearMap.lsmul ℝ ℝ) volume =
              MeasureTheory.convolution (periodise ρ ε)
                (fun y => (f y - g y) + g y)
                (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
            congr 2
            funext y
            ring_nf
          _ = _ := hadd
      have hsum : eLpNorm
          (fun x => spaceTimeConvolution (periodise ρ ε) f x - f x)
          (ENNReal.ofReal p) ≤
          eLpNorm
            (fun x => spaceTimeConvolution (periodise ρ ε) (fun y => f y - g y) x)
            (ENNReal.ofReal p) +
          eLpNorm
            (fun x => spaceTimeConvolution (periodise ρ ε) g x - g x)
            (ENNReal.ofReal p) +
          eLpNorm (fun x => f x - g x) (ENNReal.ofReal p) := by
        let A : SpaceTime → ℝ :=
          fun x => spaceTimeConvolution (periodise ρ ε) (fun y => f y - g y) x
        let B' : SpaceTime → ℝ :=
          fun x => spaceTimeConvolution (periodise ρ ε) g x - g x
        let C : SpaceTime → ℝ := fun x => f x - g x
        have hfun : (fun x => spaceTimeConvolution (periodise ρ ε) f x - f x) =
            A + B' - C := by
          funext x
          dsimp [A, B', C]
          rw [hlin]
          simp only [Pi.add_apply]
          abel
        rw [hfun]
        change eLpNorm (A + B' - C) (ENNReal.ofReal p) ≤
          eLpNorm A (ENNReal.ofReal p) + eLpNorm B' (ENNReal.ofReal p) +
            eLpNorm C (ENNReal.ofReal p)
        exact constantsComparison_eLpNorm_sub_add_le hpenn
      calc
        _ ≤ a / 4 + a / 4 + a / 4 := by
          exact le_trans hsum
            (add_le_add (add_le_add hsmallε hcompactε) (hfg.trans hηle))
        _ ≤ a := by
          calc
            a / 4 + a / 4 + a / 4 = (3 / 4 : ℝ≥0∞) * a := by
              simp only [div_eq_mul_inv]
              ring
            _ ≤ a := by
              have hcoef : (3 / 4 : ℝ≥0∞) ≤ 1 := by
                calc
                  (3 : ℝ≥0∞) / 4 ≤ 4 / 4 :=
                    ENNReal.div_le_div_right (by norm_num) 4
                  _ = 1 := ENNReal.div_self (by norm_num) (by norm_num)
              simpa only [one_mul] using
                mul_le_mul_of_nonneg_right hcoef
                  (show (0 : ℝ≥0∞) ≤ a from bot_le)
    exact hfull
  exact hwork

end RegularityStructures.Phi43

end
