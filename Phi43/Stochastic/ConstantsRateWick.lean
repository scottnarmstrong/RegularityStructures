/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsRateMollifyKernels
public import Phi43.Stochastic.ConstantsComparisonWick
public import Phi43.Stochastic.ConstantsComparisonHairerMollifiedBound
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import RegularityStructures.Probability.AnnealedNoiseBridge

/-!
# A power rate for the Wick-constant comparison

`constantsRate_wick`: `|C₁^ε - C̃₁^ε - L₁| ≤ C ε^{1/6}` for `ε ∈ (0, 1]`, where
`C₁^ε - C̃₁^ε = ∫ R_ε P_ε` with `R_ε = ρ_ε^♯ * R ∈ L³` and `P_ε = ρ_ε^♯ * P ∈ L^{3/2}`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures.Phi43

open RegularityStructures

theorem constantsRate_hairerSq_integrable (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ)
    (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Integrable (fun z : SpaceTime => hairerMollifiedKernel N ρ ε z ^ 2) := by
  have hkernel := integrable_constantsComparison_hairerKernelTorus N
  have hperiod := integrable_periodise ρ hρ hε
  have hhairer : Integrable (hairerMollifiedKernel N ρ ε) := by
    rw [← constantsComparison_hairerMollifiedKernel_eq_convolution N ρ]
    exact hperiod.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hkernel
  obtain ⟨C, hC, hbound⟩ := hairerMollifiedKernel_singular_bound ρ hρ N
  have htop : MemLp (hairerMollifiedKernel N ρ ε) ⊤ := by
    have hmeas : AEStronglyMeasurable (hairerMollifiedKernel N ρ ε)
        (volume : Measure SpaceTime) := by
      rw [← constantsComparison_hairerMollifiedKernel_eq_convolution N ρ]
      exact (measurable_periodise ρ hρ).aestronglyMeasurable.convolution
        (ContinuousLinearMap.lsmul ℝ ℝ)
        (measurable_constantsComparison_hairerKernelTorus N).aestronglyMeasurable
    apply memLp_top_of_bound hmeas (C * ε ^ (-(3 : ℝ)))
    filter_upwards [] with z
    have hpos : 0 < torusParabolicSize z + ε :=
      add_pos_of_nonneg_of_pos (torusParabolicSize_nonneg z) hε
    have hpow : (torusParabolicSize z + ε) ^ (-(3 : ℝ)) ≤ ε ^ (-(3 : ℝ)) := by
      exact Real.rpow_le_rpow_of_nonpos hε
        (le_add_of_nonneg_left (torusParabolicSize_nonneg z)) (by norm_num)
    have hpoint := hbound hε hε1 z
    have hfinal : |hairerMollifiedKernel N ρ ε z| ≤ C * ε ^ (-(3 : ℝ)) :=
      hpoint.trans (mul_le_mul_of_nonneg_left hpow hC)
    simpa only [Real.norm_eq_abs] using hfinal
  have hone : MemLp (hairerMollifiedKernel N ρ ε) 1 :=
    memLp_one_iff_integrable.mpr hhairer
  have hsq := htop.integrable_mul hone
  change Integrable ((fun z => hairerMollifiedKernel N ρ ε z) *
    hairerMollifiedKernel N ρ ε) at hsq
  exact hsq.congr (Filter.Eventually.of_forall fun z => by simp [pow_two])

theorem constantsRate_enorm_le_real {x t : ℝ} {A : ℝ≥0∞} (ht : 0 ≤ t) (hA : A ≠ ⊤)
    (h : ‖x‖ₑ ≤ ENNReal.ofReal t * A) : |x| ≤ t * A.toReal := by
  have h1 : ENNReal.ofReal |x| ≤ ENNReal.ofReal t * A := by
    rwa [← Real.enorm_eq_ofReal_abs]
  have h2 : (ENNReal.ofReal |x|).toReal ≤ (ENNReal.ofReal t * A).toReal :=
    ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA) h1
  rwa [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal ht] at h2

private theorem eLpNorm_add_le_aux {f g : SpaceTime → ℝ} {p : ℝ} (hp : 1 ≤ p) :
    eLpNorm (fun z => f z + g z) (ENNReal.ofReal p) volume ≤
      eLpNorm f (ENNReal.ofReal p) volume + eLpNorm g (ENNReal.ofReal p) volume :=
  eLpNorm_add_le (ENNReal.one_le_ofReal.mpr hp)

theorem constantsRate_wick (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) :
    ∃ C θ' : ℝ, 0 < θ' ∧ ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
      |wickConstant ρ ε - hairerWickConstant N ρ ε - constantsComparison_wickLimit N| ≤
        C * ε ^ θ' := by
  obtain ⟨cR, hcR, hR⟩ := constantsRate_remainder_rate N ρ hρ
  obtain ⟨cG, hcG, hG⟩ := constantsRate_massive_rate ρ hρ
  obtain ⟨cK, hcK, hK⟩ := constantsRate_hairer_rate N ρ hρ
  obtain ⟨MG, hMG, hUG⟩ := constantsRate_massive_unif ρ hρ
  obtain ⟨MK, hMK, hUK⟩ := constantsRate_hairer_unif N ρ hρ
  obtain ⟨MR, hMR, hUR⟩ := constantsRate_remainder_unif N ρ hρ
  have hRmem : MemLp (constantsComparisonR N) (ENNReal.ofReal 3) := constantsRate_R_memLp N
  have hGmem := constantsRate_massive_memLp
  have hKmem := constantsRate_hairer_memLp N
  set nR : ℝ≥0∞ := eLpNorm (constantsComparisonR N) (ENNReal.ofReal 3) volume with hnR
  set nG : ℝ≥0∞ := eLpNorm massiveHeatKernel (ENNReal.ofReal (3 / 2)) volume with hnG
  set nK : ℝ≥0∞ := eLpNorm (hairerKernelTorus N) (ENNReal.ofReal (3 / 2)) volume with hnK
  have hnRt : nR ≠ ⊤ := hRmem.eLpNorm_lt_top.ne
  have hnGt : nG ≠ ⊤ := hGmem.eLpNorm_lt_top.ne
  have hnKt : nK ≠ ⊤ := hKmem.eLpNorm_lt_top.ne
  let Cenn : ℝ≥0∞ := ENNReal.ofReal cR * (ENNReal.ofReal MG * nG + ENNReal.ofReal MK * nK) +
    nR * ENNReal.ofReal (cG + cK)
  have hCenn : Cenn ≠ ⊤ := by
    apply ENNReal.add_ne_top.mpr
    constructor
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hnGt,
          ENNReal.mul_ne_top ENNReal.ofReal_ne_top hnKt⟩)
    · exact ENNReal.mul_ne_top hnRt ENNReal.ofReal_ne_top
  refine ⟨Cenn.toReal, 1 / 6, by norm_num, ?_⟩
  intro ε hε
  obtain ⟨hε0, hε1⟩ := hε
  set t : ℝ := ε ^ (1 / 6 : ℝ) with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg hε0.le _
  have ht3 : ε ^ (1 / 3 : ℝ) ≤ t := by
    rw [ht]
    exact Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (by norm_num)
  -- memberships
  have hGε : MemLp (mollifiedKernel ρ ε) (ENNReal.ofReal (3 / 2)) :=
    memLp_iff.mpr (lt_of_le_of_lt (hUG ε hε0 hε1)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hGmem.eLpNorm_lt_top))
  have hKε : MemLp (hairerMollifiedKernel N ρ ε) (ENNReal.ofReal (3 / 2)) :=
    memLp_iff.mpr (lt_of_le_of_lt (hUK ε hε0 hε1)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKmem.eLpNorm_lt_top))
  have hRε : MemLp (wickComparisonR N ρ ε) (ENNReal.ofReal 3) :=
    memLp_iff.mpr (lt_of_le_of_lt (hUR ε hε0 hε1)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hRmem.eLpNorm_lt_top))
  set Pε : SpaceTime → ℝ := fun z => mollifiedKernel ρ ε z + hairerMollifiedKernel N ρ ε z
    with hPε
  set P : SpaceTime → ℝ := fun z => massiveHeatKernel z + hairerKernelTorus N z with hP
  have hPεmem : MemLp Pε (ENNReal.ofReal (3 / 2)) := hGε.add hKε
  have hPmem : MemLp P (ENNReal.ofReal (3 / 2)) := hGmem.add hKmem
  have hRdiff : MemLp (fun z => wickComparisonR N ρ ε z - constantsComparisonR N z)
      (ENNReal.ofReal 3) := hRε.sub hRmem
  have hPdiff : MemLp (fun z => Pε z - P z) (ENNReal.ofReal (3 / 2)) := hPεmem.sub hPmem
  -- the identity for the constants
  have hGsq := (constants_finite ρ hρ ⟨hε0, hε1⟩).2.2.2.2.2.2.1
  have hKsq := constantsRate_hairerSq_integrable N ρ hρ hε0 hε1
  have hdiff1 := wickConstant_sub_hairerWickConstant_integrand N ρ ε hGsq hKsq
  have hP' : wickComparisonP N ρ ε = Pε := rfl
  have hHold : (ENNReal.ofReal 3).HolderTriple (ENNReal.ofReal (3 / 2)) 1 :=
    constantsRate_holder_three.ennrealOfReal
  have hint1 : Integrable (fun z => wickComparisonR N ρ ε z * Pε z) :=
    hRε.integrable_mul hPεmem
  have hint2 : Integrable (fun z => constantsComparisonR N z * P z) :=
    hRmem.integrable_mul hPmem
  have hint3 : Integrable (fun z => (wickComparisonR N ρ ε z - constantsComparisonR N z) * Pε z) :=
    hRdiff.integrable_mul hPεmem
  have hint4 : Integrable (fun z => constantsComparisonR N z * (Pε z - P z)) :=
    hRmem.integrable_mul hPdiff
  have hsplit : wickConstant ρ ε - hairerWickConstant N ρ ε - constantsComparison_wickLimit N =
      (∫ z, (wickComparisonR N ρ ε z - constantsComparisonR N z) * Pε z) +
        ∫ z, constantsComparisonR N z * (Pε z - P z) := by
    rw [hdiff1, constantsComparison_wickLimit]
    change (∫ z, wickComparisonR N ρ ε z * Pε z) - ∫ z, constantsComparisonR N z * P z = _
    rw [← integral_sub hint1 hint2, ← integral_add hint3 hint4]
    apply integral_congr_ae
    filter_upwards [] with z
    ring
  -- Hölder estimates
  have hb1 : ‖∫ z, (wickComparisonR N ρ ε z - constantsComparisonR N z) * Pε z‖ₑ ≤
      eLpNorm (fun z => wickComparisonR N ρ ε z - constantsComparisonR N z)
        (ENNReal.ofReal 3) volume * eLpNorm Pε (ENNReal.ofReal (3 / 2)) volume := by
    have := (constantsRate_corr_bound constantsRate_holder_three hRdiff hPεmem 0).2
    simpa only [zero_add] using this
  have hb2 : ‖∫ z, constantsComparisonR N z * (Pε z - P z)‖ₑ ≤
      nR * eLpNorm (fun z => Pε z - P z) (ENNReal.ofReal (3 / 2)) volume := by
    have := (constantsRate_corr_bound constantsRate_holder_three hRmem hPdiff 0).2
    simpa only [zero_add] using this
  have ha1 : eLpNorm (fun z => wickComparisonR N ρ ε z - constantsComparisonR N z)
      (ENNReal.ofReal 3) volume ≤ ENNReal.ofReal (cR * t) := by
    simpa [ht] using hR ε hε0 hε1
  have ha2 : eLpNorm Pε (ENNReal.ofReal (3 / 2)) volume ≤
      ENNReal.ofReal MG * nG + ENNReal.ofReal MK * nK := by
    refine (eLpNorm_add_le_aux (by norm_num)).trans ?_
    exact add_le_add (hUG ε hε0 hε1) (hUK ε hε0 hε1)
  have ha3 : eLpNorm (fun z => Pε z - P z) (ENNReal.ofReal (3 / 2)) volume ≤
      ENNReal.ofReal ((cG + cK) * t) := by
    have e : (fun z => Pε z - P z) = fun z =>
        (mollifiedKernel ρ ε z - massiveHeatKernel z) +
          (hairerMollifiedKernel N ρ ε z - hairerKernelTorus N z) := by
      funext z
      simp only [hPε, hP]
      ring
    rw [e]
    have hGd : MemLp (fun z => mollifiedKernel ρ ε z - massiveHeatKernel z)
        (ENNReal.ofReal (3 / 2)) := hGε.sub hGmem
    have hKd : MemLp (fun z => hairerMollifiedKernel N ρ ε z - hairerKernelTorus N z)
        (ENNReal.ofReal (3 / 2)) := hKε.sub hKmem
    refine (eLpNorm_add_le_aux (by norm_num)).trans ?_
    have h1 := hG ε hε0 hε1
    have h2 := hK ε hε0 hε1
    have h3 : ENNReal.ofReal (cG * ε ^ (1 / 3 : ℝ)) ≤ ENNReal.ofReal (cG * t) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ht3 hcG)
    have h4 : ENNReal.ofReal (cK * ε ^ (1 / 3 : ℝ)) ≤ ENNReal.ofReal (cK * t) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ht3 hcK)
    calc
      _ ≤ ENNReal.ofReal (cG * t) + ENNReal.ofReal (cK * t) :=
        add_le_add (h1.trans h3) (h2.trans h4)
      _ = ENNReal.ofReal ((cG + cK) * t) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
  have hbound : ‖wickConstant ρ ε - hairerWickConstant N ρ ε - constantsComparison_wickLimit N‖ₑ ≤
      ENNReal.ofReal t * Cenn := by
    rw [hsplit]
    refine (enorm_add_le _ _).trans ?_
    have e1 : ‖∫ z, (wickComparisonR N ρ ε z - constantsComparisonR N z) * Pε z‖ₑ ≤
        ENNReal.ofReal (cR * t) * (ENNReal.ofReal MG * nG + ENNReal.ofReal MK * nK) :=
      hb1.trans (mul_le_mul' ha1 ha2)
    have e2 : ‖∫ z, constantsComparisonR N z * (Pε z - P z)‖ₑ ≤
        nR * ENNReal.ofReal ((cG + cK) * t) := hb2.trans (mul_le_mul' le_rfl ha3)
    refine (add_le_add e1 e2).trans (le_of_eq ?_)
    simp only [Cenn]
    rw [ENNReal.ofReal_mul hcR, ENNReal.ofReal_mul (by positivity : 0 ≤ cG + cK)]
    ring
  have := constantsRate_enorm_le_real ht0 hCenn hbound
  calc
    _ ≤ t * Cenn.toReal := this
    _ = Cenn.toReal * ε ^ (1 / 6 : ℝ) := by rw [ht]; ring

end RegularityStructures.Phi43

end
