/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsRateSunsetId
public import Phi43.Stochastic.ConstantsComparisonC2Majorants

/-!
# The Hölder estimate for the second-constant comparison at a fixed scale

For `ε ∈ (0, 1]`, the difference of the sunset constants at scale `ε` and its limit is bounded by
an explicit expression in `L^{3/2}`, `L³` norms of the kernels, their mollifications and the
mollification errors.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures.Phi43

open RegularityStructures

theorem constantsRate_holderTriple_333 :
    (ENNReal.ofReal 3).HolderTriple (ENNReal.ofReal 3) (ENNReal.ofReal (3 / 2)) := by
  constructor
  rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 3),
    ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 3 / 2),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  congr 1
  norm_num

theorem constantsRate_sunset_bounds (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {aR aG aK uG uK uR nR nG nK : ℝ≥0∞}
    (haR : eLpNorm (fun z => wickComparisonR N ρ ε z - constantsComparisonR N z)
      (ENNReal.ofReal 3) volume ≤ aR)
    (haG : eLpNorm (fun z => mollifiedKernel ρ ε z - massiveHeatKernel z)
      (ENNReal.ofReal (3 / 2)) volume ≤ aG)
    (haK : eLpNorm (fun z => hairerMollifiedKernel N ρ ε z - hairerKernelTorus N z)
      (ENNReal.ofReal (3 / 2)) volume ≤ aK)
    (huG : eLpNorm (mollifiedKernel ρ ε) (ENNReal.ofReal (3 / 2)) volume ≤ uG)
    (huK : eLpNorm (hairerMollifiedKernel N ρ ε) (ENNReal.ofReal (3 / 2)) volume ≤ uK)
    (huR : eLpNorm (wickComparisonR N ρ ε) (ENNReal.ofReal 3) volume ≤ uR)
    (hnR : eLpNorm (constantsComparisonR N) (ENNReal.ofReal 3) volume ≤ nR)
    (hnG : eLpNorm massiveHeatKernel (ENNReal.ofReal (3 / 2)) volume ≤ nG)
    (hnK : eLpNorm (hairerKernelTorus N) (ENNReal.ofReal (3 / 2)) volume ≤ nK) :
    MemLp constantsComparison_covarianceLimit (ENNReal.ofReal 3) ∧
    MemLp (constantsComparison_hairerCovarianceLimit N) (ENNReal.ofReal 3) ∧
    MemLp (covariance ρ ε) (ENNReal.ofReal 3) ∧
    MemLp (hairerCovariance N ρ ε) (ENNReal.ofReal 3) ∧
    eLpNorm constantsComparison_covarianceLimit (ENNReal.ofReal 3) volume ≤ nG * nG ∧
    eLpNorm (constantsComparison_hairerCovarianceLimit N) (ENNReal.ofReal 3) volume ≤ nK * nK ∧
    eLpNorm (covariance ρ ε) (ENNReal.ofReal 3) volume ≤ uG * uG ∧
    eLpNorm (hairerCovariance N ρ ε) (ENNReal.ofReal 3) volume ≤ uK * uK ∧
    eLpNorm (fun z => covariance ρ ε z - constantsComparison_covarianceLimit z)
      (ENNReal.ofReal 3) volume ≤ aG * uG + nG * aG ∧
    eLpNorm (fun z => hairerCovariance N ρ ε z - constantsComparison_hairerCovarianceLimit N z)
      (ENNReal.ofReal 3) volume ≤ aK * uK + nK * aK ∧
    (∀ z, ‖(constantsRateCorr (wickComparisonR N ρ ε) (mollifiedKernel ρ ε) z +
        constantsRateCorr (hairerMollifiedKernel N ρ ε) (wickComparisonR N ρ ε) z) -
      (constantsRateCorr (constantsComparisonR N) massiveHeatKernel z +
        constantsRateCorr (hairerKernelTorus N) (constantsComparisonR N) z)‖ₑ ≤
      aR * uG + nR * aG + (aK * uR + nK * aR)) ∧
    (∀ z, ‖constantsRateCorr (constantsComparisonR N) massiveHeatKernel z +
        constantsRateCorr (hairerKernelTorus N) (constantsComparisonR N) z‖ₑ ≤
      nR * nG + nK * nR) := by
  have hG := constantsRate_massive_memLp
  have hK := constantsRate_hairer_memLp N
  have hR := constantsRate_R_memLp N
  have hGe32 := constantsRate_massiveMollified_memLp ρ hρ hε hε1
  have hKe32 := constantsRate_hairerMollified_memLp N ρ hρ hε hε1
  have hRe := constantsRate_remainderMollified_memLp N ρ hρ hε hε1
  have mG := measurable_massiveHeatKernel
  have mK := measurable_constantsComparison_hairerKernelTorus N
  have mGe := constantsRate_massiveMollified_measurable ρ hρ hε
  have mKe := constantsRate_hairerMollified_measurable N ρ hρ hε
  have yGG := constantsRate_corr_young mG mG hG hG
  have yKK := constantsRate_corr_young mK mK hK hK
  have yGeGe := constantsRate_corr_young mGe mGe hGe32 hGe32
  have yKeKe := constantsRate_corr_young mKe mKe hKe32 hKe32
  have hdG : Measurable (fun x => mollifiedKernel ρ ε x - massiveHeatKernel x) := mGe.sub mG
  have hdK : Measurable (fun x => hairerMollifiedKernel N ρ ε x - hairerKernelTorus N x) :=
    mKe.sub mK
  refine ⟨yGG.2.1, yKK.2.1, yGeGe.2.1, yKeKe.2.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact yGG.2.2.trans (mul_le_mul' hnG hnG)
  · exact yKK.2.2.trans (mul_le_mul' hnK hnK)
  · exact yGeGe.2.2.trans (mul_le_mul' huG huG)
  · exact yKeKe.2.2.trans (mul_le_mul' huK huK)
  · have hae := constantsRate_cov_sub_limit_ae ρ hρ hε hε1
    have y1 := constantsRate_corr_young hdG mGe (hGe32.sub hG) hGe32
    have y2 := constantsRate_corr_young mG hdG hG (hGe32.sub hG)
    calc
      eLpNorm (fun z => covariance ρ ε z - constantsComparison_covarianceLimit z)
          (ENNReal.ofReal 3) volume =
          eLpNorm (fun z => constantsRateCorr (fun x => mollifiedKernel ρ ε x - massiveHeatKernel x)
            (mollifiedKernel ρ ε) z + constantsRateCorr massiveHeatKernel
            (fun x => mollifiedKernel ρ ε x - massiveHeatKernel x) z) (ENNReal.ofReal 3) volume :=
        eLpNorm_congr_ae hae
      _ ≤ _ := constantsRate_eLpNorm_add_le (by norm_num)
      _ ≤ aG * uG + nG * aG :=
        add_le_add (y1.2.2.trans (mul_le_mul' haG huG)) (y2.2.2.trans (mul_le_mul' hnG haG))
  · have hae := constantsRate_hcov_sub_limit_ae N ρ hρ hε hε1
    have y1 := constantsRate_corr_young hdK mKe (hKe32.sub hK) hKe32
    have y2 := constantsRate_corr_young mK hdK hK (hKe32.sub hK)
    calc
      eLpNorm (fun z => hairerCovariance N ρ ε z - constantsComparison_hairerCovarianceLimit N z)
          (ENNReal.ofReal 3) volume =
          eLpNorm (fun z => constantsRateCorr
            (fun x => hairerMollifiedKernel N ρ ε x - hairerKernelTorus N x)
            (hairerMollifiedKernel N ρ ε) z + constantsRateCorr (hairerKernelTorus N)
            (fun x => hairerMollifiedKernel N ρ ε x - hairerKernelTorus N x) z)
            (ENNReal.ofReal 3) volume :=
        eLpNorm_congr_ae hae
      _ ≤ _ := constantsRate_eLpNorm_add_le (by norm_num)
      _ ≤ aK * uK + nK * aK :=
        add_le_add (y1.2.2.trans (mul_le_mul' haK huK)) (y2.2.2.trans (mul_le_mul' hnK haK))
  · intro z
    have e1 := constantsRate_corr_diff_bound (a := constantsComparisonR N)
      (a' := wickComparisonR N ρ ε) (b := massiveHeatKernel) (b' := mollifiedKernel ρ ε)
      hR hRe hG hGe32 z
    have e2 := constantsRate_corr_diff_bound' (a := hairerKernelTorus N)
      (a' := hairerMollifiedKernel N ρ ε) (b := constantsComparisonR N)
      (b' := wickComparisonR N ρ ε) hK hKe32 hR hRe z
    have hsplit : (constantsRateCorr (wickComparisonR N ρ ε) (mollifiedKernel ρ ε) z +
        constantsRateCorr (hairerMollifiedKernel N ρ ε) (wickComparisonR N ρ ε) z) -
        (constantsRateCorr (constantsComparisonR N) massiveHeatKernel z +
        constantsRateCorr (hairerKernelTorus N) (constantsComparisonR N) z) =
        (constantsRateCorr (wickComparisonR N ρ ε) (mollifiedKernel ρ ε) z -
          constantsRateCorr (constantsComparisonR N) massiveHeatKernel z) +
        (constantsRateCorr (hairerMollifiedKernel N ρ ε) (wickComparisonR N ρ ε) z -
          constantsRateCorr (hairerKernelTorus N) (constantsComparisonR N) z) := by ring
    rw [hsplit]
    refine (enorm_add_le _ _).trans ?_
    have f1 : ‖constantsRateCorr (wickComparisonR N ρ ε) (mollifiedKernel ρ ε) z -
        constantsRateCorr (constantsComparisonR N) massiveHeatKernel z‖ₑ ≤ aR * uG + nR * aG :=
      e1.trans (add_le_add (mul_le_mul' haR huG) (mul_le_mul' hnR haG))
    have f2 : ‖constantsRateCorr (hairerMollifiedKernel N ρ ε) (wickComparisonR N ρ ε) z -
        constantsRateCorr (hairerKernelTorus N) (constantsComparisonR N) z‖ₑ ≤
        aK * uR + nK * aR :=
      e2.trans (add_le_add (mul_le_mul' haK huR) (mul_le_mul' hnK haR))
    exact add_le_add f1 f2
  · intro z
    refine (enorm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (constantsRate_corr_bound constantsRate_holder_three hR hG z).2.trans
        (mul_le_mul' hnR hnG)
    · exact (constantsRate_corr_bound constantsRate_holder_three_halves hK hR z).2.trans
        (mul_le_mul' hnK hnR)

theorem constantsRate_sunset_estimate (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {aR aG aK uG uK uR nR nG nK : ℝ≥0∞}
    (haR : eLpNorm (fun z => wickComparisonR N ρ ε z - constantsComparisonR N z)
      (ENNReal.ofReal 3) volume ≤ aR)
    (haG : eLpNorm (fun z => mollifiedKernel ρ ε z - massiveHeatKernel z)
      (ENNReal.ofReal (3 / 2)) volume ≤ aG)
    (haK : eLpNorm (fun z => hairerMollifiedKernel N ρ ε z - hairerKernelTorus N z)
      (ENNReal.ofReal (3 / 2)) volume ≤ aK)
    (huG : eLpNorm (mollifiedKernel ρ ε) (ENNReal.ofReal (3 / 2)) volume ≤ uG)
    (huK : eLpNorm (hairerMollifiedKernel N ρ ε) (ENNReal.ofReal (3 / 2)) volume ≤ uK)
    (huR : eLpNorm (wickComparisonR N ρ ε) (ENNReal.ofReal 3) volume ≤ uR)
    (hnR : eLpNorm (constantsComparisonR N) (ENNReal.ofReal 3) volume ≤ nR)
    (hnG : eLpNorm massiveHeatKernel (ENNReal.ofReal (3 / 2)) volume ≤ nG)
    (hnK : eLpNorm (hairerKernelTorus N) (ENNReal.ofReal (3 / 2)) volume ≤ nK)
    (hfin : aR ≠ ⊤ ∧ aG ≠ ⊤ ∧ aK ≠ ⊤ ∧ uG ≠ ⊤ ∧ uK ≠ ⊤ ∧ uR ≠ ⊤ ∧ nR ≠ ⊤ ∧ nG ≠ ⊤ ∧
      nK ≠ ⊤) :
    ‖sunsetConstant ρ ε - hairerSunsetConstant N ρ ε - constantsComparison_sunsetLimit N‖ₑ ≤
      2 * (nR * ((aG * uG + nG * aG) * (uG * uG + nG * nG))) +
      2 * ((aR * uG + nR * aG + (aK * uR + nK * aR)) * (nK * (uG * uG + uK * uK)) +
        (nR * nG + nK * nR) * (nK * ((aG * uG + nG * aG) + (aK * uK + nK * aK)))) := by
  obtain ⟨hQm, hPm, hQem, hPem, eQ, eP, eQe, ePe, eQd, ePd, hDd, hDb⟩ :=
    constantsRate_sunset_bounds N ρ hρ hε hε1 haR haG haK huG huK huR hnR hnG hnK
  obtain ⟨haRt, haGt, haKt, huGt, huKt, huRt, hnRt, hnGt, hnKt⟩ := hfin
  obtain ⟨hG', hK', hR', hD'⟩ := constantsComparison_C2_integrability N ρ hρ hε hε1
  have hid := sunsetConstant_sub_hairerSunsetConstant_integrand N ρ ε hG' hK' hR' hD'
  have hR3 := constantsRate_R_memLp N
  have hK32 := constantsRate_hairer_memLp N
  have mK := measurable_constantsComparison_hairerKernelTorus N
  have hT333 := constantsRate_holderTriple_333
  have hT3 : (ENNReal.ofReal 3).HolderTriple (ENNReal.ofReal (3 / 2)) 1 :=
    constantsRate_holder_three.ennrealOfReal
  have hT32 : (ENNReal.ofReal (3 / 2)).HolderTriple (ENNReal.ofReal 3) 1 :=
    constantsRate_holder_three_halves.ennrealOfReal
  set Dsup : ℝ≥0∞ := nR * nG + nK * nR with hDsup
  set Δ : ℝ≥0∞ := aR * uG + nR * aG + (aK * uR + nK * aR) with hΔ
  have hDsupt : Dsup ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top hnRt hnGt,
    ENNReal.mul_ne_top hnKt hnRt⟩
  have hΔt : Δ ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top haRt huGt, ENNReal.mul_ne_top hnRt haGt⟩,
    ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top haKt huRt, ENNReal.mul_ne_top hnKt haRt⟩⟩
  -- the identities for the covariances
  have hI1 := constantsRate_cov_sub_eq N ρ hρ hε hε1
  have hI2 := constantsRate_covLimit_sub_eq N
  -- limit integrability
  have hRQ : Integrable (fun z => constantsComparisonR N z *
      constantsComparison_covarianceLimit z ^ 2) := by
    have := hR3.integrable_mul (hQm.mul (r := ENNReal.ofReal (3 / 2)) hQm)
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp [pow_two]
  have hKQ : Integrable (fun z => hairerKernelTorus N z *
      (constantsComparison_covarianceLimit z - constantsComparison_hairerCovarianceLimit N z) *
      (constantsComparison_covarianceLimit z + constantsComparison_hairerCovarianceLimit N z)) := by
    have h1 := hK32.integrable_mul (hQm.add hPm)
    have hbd : ∀ᵐ z : SpaceTime ∂volume,
        ‖constantsComparison_covarianceLimit z -
          constantsComparison_hairerCovarianceLimit N z‖ ≤ Dsup.toReal := by
      filter_upwards [hI2] with z hz
      rw [hz]
      exact constantsRate_norm_le_of_enorm_le hDsupt (hDb z)
    have h2 := Integrable.bdd_mul h1 (hQm.sub hPm).aestronglyMeasurable hbd
    refine h2.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply]
    ring
  have hsplit : sunsetConstant ρ ε - hairerSunsetConstant N ρ ε -
      constantsComparison_sunsetLimit N =
      2 * ((∫ z, constantsComparisonR N z * covariance ρ ε z ^ 2) -
        ∫ z, constantsComparisonR N z * constantsComparison_covarianceLimit z ^ 2) +
      2 * ((∫ z, hairerKernelTorus N z * (covariance ρ ε z - hairerCovariance N ρ ε z) *
          (covariance ρ ε z + hairerCovariance N ρ ε z)) -
        ∫ z, hairerKernelTorus N z * (constantsComparison_covarianceLimit z -
          constantsComparison_hairerCovarianceLimit N z) *
          (constantsComparison_covarianceLimit z +
            constantsComparison_hairerCovarianceLimit N z)) := by
    rw [hid, constantsComparison_sunsetLimit]
    ring
  have hA : ‖(∫ z, constantsComparisonR N z * covariance ρ ε z ^ 2) -
      ∫ z, constantsComparisonR N z * constantsComparison_covarianceLimit z ^ 2‖ₑ ≤
      nR * ((aG * uG + nG * aG) * (uG * uG + nG * nG)) := by
    rw [← integral_sub hR' hRQ]
    have e : (fun z => constantsComparisonR N z * covariance ρ ε z ^ 2 -
        constantsComparisonR N z * constantsComparison_covarianceLimit z ^ 2) =
        fun z => constantsComparisonR N z *
          ((covariance ρ ε z - constantsComparison_covarianceLimit z) *
            (covariance ρ ε z + constantsComparison_covarianceLimit z)) := by
      funext z
      ring
    rw [e]
    refine (constantsRate_enorm_integral_mul_three_le hR3 (hQem.sub hQm) (hQem.add hQm)).trans ?_
    have hsum : eLpNorm (fun z => covariance ρ ε z + constantsComparison_covarianceLimit z)
        (ENNReal.ofReal 3) volume ≤ uG * uG + nG * nG :=
      (constantsRate_eLpNorm_add_le (by norm_num)).trans (add_le_add eQe eQ)
    exact mul_le_mul' hnR (mul_le_mul' eQd hsum)
  have hB : ‖(∫ z, hairerKernelTorus N z * (covariance ρ ε z - hairerCovariance N ρ ε z) *
          (covariance ρ ε z + hairerCovariance N ρ ε z)) -
        ∫ z, hairerKernelTorus N z * (constantsComparison_covarianceLimit z -
          constantsComparison_hairerCovarianceLimit N z) *
          (constantsComparison_covarianceLimit z +
            constantsComparison_hairerCovarianceLimit N z)‖ₑ ≤
      Δ * (nK * (uG * uG + uK * uK)) +
        Dsup * (nK * ((aG * uG + nG * aG) + (aK * uK + nK * aK))) := by
    rw [← integral_sub hD' hKQ]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    let w1 : SpaceTime → ℝ := fun z => (covariance ρ ε z - hairerCovariance N ρ ε z) -
      (constantsComparison_covarianceLimit z - constantsComparison_hairerCovarianceLimit N z)
    let w2 : SpaceTime → ℝ := fun z => constantsComparison_covarianceLimit z -
      constantsComparison_hairerCovarianceLimit N z
    let Se : SpaceTime → ℝ := fun z => covariance ρ ε z + hairerCovariance N ρ ε z
    let S : SpaceTime → ℝ := fun z => constantsComparison_covarianceLimit z +
      constantsComparison_hairerCovarianceLimit N z
    have hpt : ∀ z, ‖hairerKernelTorus N z * (covariance ρ ε z - hairerCovariance N ρ ε z) *
          (covariance ρ ε z + hairerCovariance N ρ ε z) -
        hairerKernelTorus N z * (constantsComparison_covarianceLimit z -
          constantsComparison_hairerCovarianceLimit N z) *
          (constantsComparison_covarianceLimit z +
            constantsComparison_hairerCovarianceLimit N z)‖ₑ ≤
        ‖w1 z * (hairerKernelTorus N z * Se z)‖ₑ +
          ‖w2 z * (hairerKernelTorus N z * (Se z - S z))‖ₑ := by
      intro z
      have : hairerKernelTorus N z * (covariance ρ ε z - hairerCovariance N ρ ε z) *
          (covariance ρ ε z + hairerCovariance N ρ ε z) -
        hairerKernelTorus N z * (constantsComparison_covarianceLimit z -
          constantsComparison_hairerCovarianceLimit N z) *
          (constantsComparison_covarianceLimit z +
            constantsComparison_hairerCovarianceLimit N z) =
          w1 z * (hairerKernelTorus N z * Se z) +
            w2 z * (hairerKernelTorus N z * (Se z - S z)) := by
        simp only [w1, w2, Se, S]
        ring
      rw [this]
      exact enorm_add_le _ _
    have hm1 : AEMeasurable (fun z => ‖w1 z * (hairerKernelTorus N z * Se z)‖ₑ) volume :=
      ((((hQem.sub hPem).sub (hQm.sub hPm)).aestronglyMeasurable).mul
        (mK.aestronglyMeasurable.mul (hQem.add hPem).aestronglyMeasurable)).enorm
    have hb1 : ∀ᵐ z : SpaceTime ∂volume, ‖w1 z‖ₑ ≤ Δ := by
      filter_upwards [hI2] with z hz
      have h1 : w1 z = (constantsRateCorr (wickComparisonR N ρ ε) (mollifiedKernel ρ ε) z +
          constantsRateCorr (hairerMollifiedKernel N ρ ε) (wickComparisonR N ρ ε) z) -
          (constantsRateCorr (constantsComparisonR N) massiveHeatKernel z +
            constantsRateCorr (hairerKernelTorus N) (constantsComparisonR N) z) := by
        simp only [w1]
        rw [hI1 z, hz]
      rw [h1]
      exact hDd z
    have hb2 : ∀ᵐ z : SpaceTime ∂volume, ‖w2 z‖ₑ ≤ Dsup := by
      filter_upwards [hI2] with z hz
      simp only [w2]
      rw [hz]
      exact hDb z
    have e1 := constantsRate_lintegral_weight_le (a := w1) (f := hairerKernelTorus N)
      (g := Se) hΔt hb1 hK32 (hQem.add hPem)
    have e2 := constantsRate_lintegral_weight_le (a := w2) (f := hairerKernelTorus N)
      (g := fun z => Se z - S z) hDsupt hb2 hK32
      ((hQem.add hPem).sub (hQm.add hPm))
    have hSe : eLpNorm Se (ENNReal.ofReal 3) volume ≤ uG * uG + uK * uK :=
      (constantsRate_eLpNorm_add_le (by norm_num)).trans (add_le_add eQe ePe)
    have hSd : eLpNorm (fun z => Se z - S z) (ENNReal.ofReal 3) volume ≤
        (aG * uG + nG * aG) + (aK * uK + nK * aK) := by
      have : (fun z => Se z - S z) = fun z =>
          (covariance ρ ε z - constantsComparison_covarianceLimit z) +
            (hairerCovariance N ρ ε z - constantsComparison_hairerCovarianceLimit N z) := by
        funext z
        simp only [Se, S]
        ring
      rw [this]
      exact (constantsRate_eLpNorm_add_le (by norm_num)).trans (add_le_add eQd ePd)
    calc
      ∫⁻ z, ‖hairerKernelTorus N z * (covariance ρ ε z - hairerCovariance N ρ ε z) *
          (covariance ρ ε z + hairerCovariance N ρ ε z) -
        hairerKernelTorus N z * (constantsComparison_covarianceLimit z -
          constantsComparison_hairerCovarianceLimit N z) *
          (constantsComparison_covarianceLimit z +
            constantsComparison_hairerCovarianceLimit N z)‖ₑ ≤
          ∫⁻ z, (‖w1 z * (hairerKernelTorus N z * Se z)‖ₑ +
            ‖w2 z * (hairerKernelTorus N z * (Se z - S z))‖ₑ) := lintegral_mono hpt
      _ = (∫⁻ z, ‖w1 z * (hairerKernelTorus N z * Se z)‖ₑ) +
          ∫⁻ z, ‖w2 z * (hairerKernelTorus N z * (Se z - S z))‖ₑ :=
        lintegral_add_left' hm1 _
      _ ≤ Δ * (nK * (uG * uG + uK * uK)) +
          Dsup * (nK * ((aG * uG + nG * aG) + (aK * uK + nK * aK))) := by
        refine add_le_add (e1.trans ?_) (e2.trans ?_)
        · exact mul_le_mul' le_rfl (mul_le_mul' hnK hSe)
        · exact mul_le_mul' le_rfl (mul_le_mul' hnK hSd)
  rw [hsplit]
  have h2 : ‖(2 : ℝ)‖ₑ = 2 := by
    rw [Real.enorm_eq_ofReal_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat]
  refine (enorm_add_le _ _).trans ?_
  rw [enorm_mul, enorm_mul, h2]
  exact add_le_add (mul_le_mul' le_rfl hA) (mul_le_mul' le_rfl hB)

end RegularityStructures.Phi43

end
