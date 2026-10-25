/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsComparisonSingularLp
public import Phi43.Constants.Finite
public import Phi43.Torus.KernelBoundsK3
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Phi43.Stochastic.ConstantsComparisonConvolution
public import Phi43.Stochastic.ConstantsComparisonHairerMollifiedBound
public import RegularityStructures.Probability.AnnealedNoiseBridge

/-!
# Fixed-scale bounds for the causal truncated covariance

This module proves measurability of the mollified causal truncated covariance in Hairer's
(10.41). The scale-uniform covariance difference is proved separately in
`ConstantsComparisonCovarianceUniform`.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures.Phi43

private theorem constantsComparison_hairerMollifiedKernel_continuous
    (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) {ε : ℝ}
    (hε : 0 < ε) : Continuous (hairerMollifiedKernel N ρ ε) := by
  have hK : Integrable (hairerKernelTorus N) :=
    integrable_constantsComparison_hairerKernelTorus N
  have hP : Continuous (periodise ρ ε) := continuous_periodise ρ hρ hε
  obtain ⟨B, hB⟩ := bounded_periodise ρ hρ hε
  let D : ℝ := max B 0
  have hD : 0 ≤ D := le_max_right B 0
  have hBD : B ≤ D := le_max_left B 0
  have hDbdd : BddAbove (Set.range fun z : SpaceTime =>
      ‖periodise ρ ε z‖) := by
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
  have hspace : Continuous (spaceTimeConvolution (periodise ρ ε)
      (hairerKernelTorus N)) := by
    rw [← heq]
    exact hc
  rw [← constantsComparison_hairerMollifiedKernel_eq_convolution N ρ]
  exact hspace

theorem constantsComparison_hairerCovariance_measurable
    (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hρ : IsMollifier ρ) (hε1 : ε ≤ 1) :
    Measurable (hairerCovariance N ρ ε) := by
  have hK : Continuous (hairerMollifiedKernel N ρ ε) :=
    constantsComparison_hairerMollifiedKernel_continuous N ρ hρ hε
  have hKi : Integrable (hairerMollifiedKernel N ρ ε) := by
    rw [← constantsComparison_hairerMollifiedKernel_eq_convolution N ρ]
    exact (integrable_periodise ρ hρ hε).integrable_convolution
      (ContinuousLinearMap.lsmul ℝ ℝ)
      (integrable_constantsComparison_hairerKernelTorus N)
  have hKneg : Measurable (fun z : SpaceTime => hairerMollifiedKernel N ρ ε (-z)) :=
    hK.measurable.comp measurable_neg
  obtain ⟨B, hB, hbound⟩ := hairerMollifiedKernel_singular_bound ρ hρ N
  have htopBound : BddAbove (Set.range fun z : SpaceTime =>
      ‖hairerMollifiedKernel N ρ ε z‖) := by
    refine ⟨B * ε ^ (-(3 : ℝ)), ?_⟩
    rintro _ ⟨z, rfl⟩
    have hpow : (torusParabolicSize z + ε) ^ (-(3 : ℝ)) ≤
        ε ^ (-(3 : ℝ)) := Real.rpow_le_rpow_of_nonpos hε
          (le_add_of_nonneg_left (torusParabolicSize_nonneg z)) (by norm_num)
    simpa only [Real.norm_eq_abs] using
      ((hbound hε hε1 z).trans (mul_le_mul_of_nonneg_left hpow hB))
  have htopBoundNeg : BddAbove (Set.range fun z : SpaceTime =>
      ‖hairerMollifiedKernel N ρ ε (-z)‖) := by
    refine ⟨B * ε ^ (-(3 : ℝ)), ?_⟩
    rintro _ ⟨z, rfl⟩
    have hpow : (torusParabolicSize (-z) + ε) ^ (-(3 : ℝ)) ≤
        ε ^ (-(3 : ℝ)) := Real.rpow_le_rpow_of_nonpos hε
          (le_add_of_nonneg_left (torusParabolicSize_nonneg (-z))) (by norm_num)
    simpa only [Real.norm_eq_abs] using
      ((hbound hε hε1 (-z)).trans (mul_le_mul_of_nonneg_left hpow hB))
  have hKnegc : Continuous (fun z : SpaceTime => hairerMollifiedKernel N ρ ε (-z)) :=
    hK.comp continuous_neg
  have hc := htopBoundNeg.continuous_convolution_right_of_integrable
    (ContinuousLinearMap.mul ℝ ℝ) hKi hKnegc
  have hcov_eq : MeasureTheory.convolution (hairerMollifiedKernel N ρ ε)
      (fun z => hairerMollifiedKernel N ρ ε (-z))
      (ContinuousLinearMap.mul ℝ ℝ) volume = hairerCovariance N ρ ε := by
    funext z
    rw [convolution_mul_swap]
    symm
    let e : SpaceTime ≃ᵐ SpaceTime :=
      MeasurableEquiv.mk (Homeomorph.neg SpaceTime).toEquiv
    have he : MeasurePreserving (e : SpaceTime → SpaceTime)
        (volume : Measure SpaceTime) volume := by
      simpa [e] using (Measure.measurePreserving_neg (volume : Measure SpaceTime))
    have htrans := he.integral_comp'
      (fun w => hairerMollifiedKernel N ρ ε (z - w) *
        hairerMollifiedKernel N ρ ε (-w))
    dsimp [e] at htrans
    simpa [hairerCovariance, sub_eq_add_neg] using htrans
  rw [← hcov_eq]
  exact hc.measurable

end RegularityStructures.Phi43

end
