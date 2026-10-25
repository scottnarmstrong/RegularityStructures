/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsRateSunsetAux
public import Phi43.Stochastic.ConstantsRateWick
public import Phi43.Stochastic.ConstantsComparisonC2Bounds
public import Phi43.Stochastic.ConstantsComparisonSunset
public import Phi43.Constants.Finite
public import RegularityStructures.Probability.AnnealedNoiseBridge

/-!
# Memberships and identities for the second-constant comparison

The mollified kernels lie in `L^{3/2} ∩ L³`; the covariance difference `Q_ε - P_ε` equals
`R_ε ⋆ G_ε + K_ε ⋆ R_ε` at every point, and the analogous identities for the unmollified
covariances and for the differences `Q_ε - Q`, `P_ε - P` hold almost everywhere.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures.Phi43

open RegularityStructures

theorem constantsRate_hairerMollified_continuous (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ)
    (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) : Continuous (hairerMollifiedKernel N ρ ε) := by
  have hK : Integrable (hairerKernelTorus N) :=
    integrable_constantsComparison_hairerKernelTorus N
  have hP : Continuous (periodise ρ ε) := continuous_periodise ρ hρ hε
  obtain ⟨B, hB⟩ := bounded_periodise ρ hρ hε
  let D : ℝ := max B 0
  have hBD : B ≤ D := le_max_left B 0
  have hDbdd : BddAbove (Set.range fun z : SpaceTime => ‖periodise ρ ε z‖) := by
    refine ⟨D, ?_⟩
    rintro _ ⟨z, rfl⟩
    simpa only [Real.norm_eq_abs] using (hB z).trans hBD
  have hc := hDbdd.continuous_convolution_right_of_integrable
    (ContinuousLinearMap.lsmul ℝ ℝ) hK hP
  have heq : MeasureTheory.convolution (hairerKernelTorus N) (periodise ρ ε)
      (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure SpaceTime) =
      spaceTimeConvolution (periodise ρ ε) (hairerKernelTorus N) := by
    funext z
    rw [convolution_lsmul_swap]
    simp only [spaceTimeConvolution]
    apply integral_congr_ae
    filter_upwards [] with w
    simp only [smul_eq_mul]
    ring
  have hspace : Continuous (spaceTimeConvolution (periodise ρ ε) (hairerKernelTorus N)) := by
    rw [← heq]
    exact hc
  rw [← constantsComparison_hairerMollifiedKernel_eq_convolution N ρ]
  exact hspace

theorem constantsRate_hairerMollified_bounded (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ)
    (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, ∀ z, |hairerMollifiedKernel N ρ ε z| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := hairerMollifiedKernel_singular_bound ρ hρ N
  refine ⟨C * ε ^ (-(3 : ℝ)), fun z => ?_⟩
  have hpow : (torusParabolicSize z + ε) ^ (-(3 : ℝ)) ≤ ε ^ (-(3 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hε (le_add_of_nonneg_left (torusParabolicSize_nonneg z))
      (by norm_num)
  exact (hbound hε hε1 z).trans (mul_le_mul_of_nonneg_left hpow hC)

theorem constantsRate_massiveMollified_memLp (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    MemLp (mollifiedKernel ρ ε) (ENNReal.ofReal (3 / 2)) := by
  obtain ⟨M, hM, h⟩ := constantsRate_massive_unif ρ hρ
  exact memLp_iff.mpr (lt_of_le_of_lt (h ε hε hε1)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top constantsRate_massive_memLp.eLpNorm_lt_top))

theorem constantsRate_hairerMollified_memLp (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ)
    (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    MemLp (hairerMollifiedKernel N ρ ε) (ENNReal.ofReal (3 / 2)) := by
  obtain ⟨M, hM, h⟩ := constantsRate_hairer_unif N ρ hρ
  exact memLp_iff.mpr (lt_of_le_of_lt (h ε hε hε1)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (constantsRate_hairer_memLp N).eLpNorm_lt_top))

theorem constantsRate_remainderMollified_memLp (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ)
    (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    MemLp (wickComparisonR N ρ ε) (ENNReal.ofReal 3) := by
  obtain ⟨M, hM, h⟩ := constantsRate_remainder_unif N ρ hρ
  exact memLp_iff.mpr (lt_of_le_of_lt (h ε hε hε1)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (constantsRate_R_memLp N).eLpNorm_lt_top))

theorem constantsRate_massiveMollified_memLp_three (ρ : ℝ × (Fin 3 → ℝ) → ℝ)
    (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    MemLp (mollifiedKernel ρ ε) (ENNReal.ofReal 3) := by
  obtain ⟨_, _, C, hC⟩ := mollifiedKernel_facts ρ hρ hε
  exact constantsRate_memLp_three_of_bounded (constantsRate_massiveMollified_memLp ρ hρ hε hε1) hC

theorem constantsRate_hairerMollified_memLp_three (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ)
    (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    MemLp (hairerMollifiedKernel N ρ ε) (ENNReal.ofReal 3) := by
  obtain ⟨C, hC⟩ := constantsRate_hairerMollified_bounded N ρ hρ hε hε1
  exact constantsRate_memLp_three_of_bounded (constantsRate_hairerMollified_memLp N ρ hρ hε hε1) hC

theorem constantsRate_massiveMollified_measurable (ρ : ℝ × (Fin 3 → ℝ) → ℝ)
    (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) : Measurable (mollifiedKernel ρ ε) :=
  (mollifiedKernel_facts ρ hρ hε).1.measurable

theorem constantsRate_hairerMollified_measurable (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ)
    (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) : Measurable (hairerMollifiedKernel N ρ ε) :=
  (constantsRate_hairerMollified_continuous N ρ hρ hε).measurable

theorem constantsRate_corr_integrable_ae {u v : SpaceTime → ℝ} (hu : Measurable u)
    (hv : Measurable v) (hu' : MemLp u (ENNReal.ofReal (3 / 2)))
    (hv' : MemLp v (ENNReal.ofReal (3 / 2))) :
    ∀ᵐ z : SpaceTime ∂volume, Integrable (fun w => u (z + w) * v w) :=
  (constantsRate_corr_young hu hv hu' hv').1

/-- Pointwise identity `Q_ε - P_ε = R_ε ⋆ G_ε + K_ε ⋆ R_ε`. -/
theorem constantsRate_cov_sub_eq (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (z : SpaceTime) :
    covariance ρ ε z - hairerCovariance N ρ ε z =
      constantsRateCorr (wickComparisonR N ρ ε) (mollifiedKernel ρ ε) z +
        constantsRateCorr (hairerMollifiedKernel N ρ ε) (wickComparisonR N ρ ε) z := by
  have hG32 := constantsRate_massiveMollified_memLp ρ hρ hε hε1
  have hK32 := constantsRate_hairerMollified_memLp N ρ hρ hε hε1
  have hG3 := constantsRate_massiveMollified_memLp_three ρ hρ hε hε1
  have hK3 := constantsRate_hairerMollified_memLp_three N ρ hρ hε hε1
  have h1 := (constantsRate_corr_bound constantsRate_holder_three_halves hG32 hG3 z).1
  have h2 := (constantsRate_corr_bound constantsRate_holder_three_halves hK32 hK3 z).1
  have h3 := (constantsRate_corr_bound constantsRate_holder_three_halves (hG32.sub hK32)
    hG3 z).1
  have h4 := (constantsRate_corr_bound constantsRate_holder_three_halves hK32
    (hG3.sub hK3) z).1
  have e := constantsRate_corr_sub_eq h1 h2 h3 h4
  exact e

/-- Almost-everywhere identity `Q - P = R ⋆ G + K ⋆ R` for the unmollified covariances. -/
theorem constantsRate_covLimit_sub_eq (N : ℕ) :
    ∀ᵐ z : SpaceTime ∂volume,
      constantsComparison_covarianceLimit z - constantsComparison_hairerCovarianceLimit N z =
        constantsRateCorr (constantsComparisonR N) massiveHeatKernel z +
          constantsRateCorr (hairerKernelTorus N) (constantsComparisonR N) z := by
  have hG := constantsRate_massive_memLp
  have hK := constantsRate_hairer_memLp N
  have hR := constantsRate_R_memLp N
  filter_upwards [constantsRate_corr_integrable_ae measurable_massiveHeatKernel
      measurable_massiveHeatKernel hG hG,
    constantsRate_corr_integrable_ae (measurable_constantsComparison_hairerKernelTorus N)
      (measurable_constantsComparison_hairerKernelTorus N) hK hK] with z h1 h2
  have h3 := (constantsRate_corr_bound constantsRate_holder_three hR hG z).1
  have h4 := (constantsRate_corr_bound constantsRate_holder_three_halves hK hR z).1
  exact constantsRate_corr_sub_eq (u := hairerKernelTorus N) (u' := massiveHeatKernel)
    (v := hairerKernelTorus N) (v' := massiveHeatKernel) h1 h2 h3 h4

/-- Almost-everywhere identity for `Q_ε - Q`. -/
theorem constantsRate_cov_sub_limit_ae (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᵐ z : SpaceTime ∂volume,
      covariance ρ ε z - constantsComparison_covarianceLimit z =
        constantsRateCorr (fun x => mollifiedKernel ρ ε x - massiveHeatKernel x)
          (mollifiedKernel ρ ε) z +
          constantsRateCorr massiveHeatKernel
            (fun x => mollifiedKernel ρ ε x - massiveHeatKernel x) z := by
  have hG := constantsRate_massive_memLp
  have hG32 := constantsRate_massiveMollified_memLp ρ hρ hε hε1
  have hG3 := constantsRate_massiveMollified_memLp_three ρ hρ hε hε1
  have hm := constantsRate_massiveMollified_measurable ρ hρ hε
  have hdm : Measurable (fun x => mollifiedKernel ρ ε x - massiveHeatKernel x) :=
    hm.sub measurable_massiveHeatKernel
  filter_upwards [constantsRate_corr_integrable_ae measurable_massiveHeatKernel
      measurable_massiveHeatKernel hG hG,
    constantsRate_corr_integrable_ae hdm hm (hG32.sub hG) hG32,
    constantsRate_corr_integrable_ae measurable_massiveHeatKernel hdm hG (hG32.sub hG)] with
    z h2 h3 h4
  have h1 := (constantsRate_corr_bound constantsRate_holder_three_halves hG32 hG3 z).1
  exact constantsRate_corr_sub_eq (u := massiveHeatKernel) (u' := mollifiedKernel ρ ε)
    (v := massiveHeatKernel) (v' := mollifiedKernel ρ ε) h1 h2 h3 h4

/-- Almost-everywhere identity for `P_ε - P`. -/
theorem constantsRate_hcov_sub_limit_ae (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ)
    (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᵐ z : SpaceTime ∂volume,
      hairerCovariance N ρ ε z - constantsComparison_hairerCovarianceLimit N z =
        constantsRateCorr (fun x => hairerMollifiedKernel N ρ ε x - hairerKernelTorus N x)
          (hairerMollifiedKernel N ρ ε) z +
          constantsRateCorr (hairerKernelTorus N)
            (fun x => hairerMollifiedKernel N ρ ε x - hairerKernelTorus N x) z := by
  have hK := constantsRate_hairer_memLp N
  have hK32 := constantsRate_hairerMollified_memLp N ρ hρ hε hε1
  have hK3 := constantsRate_hairerMollified_memLp_three N ρ hρ hε hε1
  have hm := constantsRate_hairerMollified_measurable N ρ hρ hε
  have hKm := measurable_constantsComparison_hairerKernelTorus N
  have hdm : Measurable (fun x => hairerMollifiedKernel N ρ ε x - hairerKernelTorus N x) :=
    hm.sub hKm
  filter_upwards [constantsRate_corr_integrable_ae hKm hKm hK hK,
    constantsRate_corr_integrable_ae hdm hm (hK32.sub hK) hK32,
    constantsRate_corr_integrable_ae hKm hdm hK (hK32.sub hK)] with z h2 h3 h4
  have h1 := (constantsRate_corr_bound constantsRate_holder_three_halves hK32 hK3 z).1
  exact constantsRate_corr_sub_eq (u := hairerKernelTorus N) (u' := hairerMollifiedKernel N ρ ε)
    (v := hairerKernelTorus N) (v' := hairerMollifiedKernel N ρ ε) h1 h2 h3 h4

end RegularityStructures.Phi43

end
