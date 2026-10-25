/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsComparisonApproxLpGeneral
public import Phi43.Stochastic.ConstantsComparisonConvolution
public import Phi43.Stochastic.ConstantsComparisonKernelMemLp
public import Phi43.Stochastic.ConstantsComparisonRemainderMemLp
public import Phi43.Stochastic.ConstantsComparisonHairerMollifiedBound
public import Phi43.Constants.Finite
import Phi43.Stochastic.ConstantsComparisonPairingLimits
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import RegularityStructures.Probability.AnnealedNoiseBridge

/-!
# Comparison of the first renormalisation constants

The difference of the Wick constants converges, by the signed Young estimate and the periodised
approximate identity applied to the `L⁴ × L^(4/3)` pairing of [Hai14, (10.33)].  The only singular
input is the order-one remainder estimate proved in `ConstantsComparisonRemainderBound` and
`ConstantsComparisonRemainderMemLp`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace RegularityStructures.Phi43

private theorem constantsComparison_convolution_difference_eq
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) {ε : ℝ}
    (f g : SpaceTime → ℝ)
    (hconvf : ∀ z : SpaceTime, Integrable
      (fun w => periodise ρ ε w * f (z - w)))
    (hconvg : ∀ z : SpaceTime, Integrable
      (fun w => periodise ρ ε w * g (z - w))) :
    spaceTimeConvolution (periodise ρ ε) (f - g) =
      spaceTimeConvolution (periodise ρ ε) f -
        spaceTimeConvolution (periodise ρ ε) g := by
  funext z
  change (∫ w, periodise ρ ε w * (f (z - w) - g (z - w))) =
    (∫ w, periodise ρ ε w * f (z - w)) -
      ∫ w, periodise ρ ε w * g (z - w)
  calc
    _ = ∫ w, (periodise ρ ε w * f (z - w)) -
        (periodise ρ ε w * g (z - w)) := by
          apply integral_congr_ae
          filter_upwards [] with w
          ring
    _ = _ := integral_sub (hconvf z) (hconvg z)

private theorem constantsComparison_convolution_add_eq
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) {ε : ℝ}
    (f g : SpaceTime → ℝ)
    (hconvf : ∀ z : SpaceTime, Integrable
      (fun w => periodise ρ ε w * f (z - w)))
    (hconvg : ∀ z : SpaceTime, Integrable
      (fun w => periodise ρ ε w * g (z - w))) :
    spaceTimeConvolution (periodise ρ ε) (f + g) =
      spaceTimeConvolution (periodise ρ ε) f +
        spaceTimeConvolution (periodise ρ ε) g := by
  funext z
  change (∫ w, periodise ρ ε w * (f (z - w) + g (z - w))) =
    (∫ w, periodise ρ ε w * f (z - w)) +
      ∫ w, periodise ρ ε w * g (z - w)
  rw [← integral_add (hconvf z) (hconvg z)]
  apply integral_congr_ae
  filter_upwards [] with w
  ring

private theorem constantsComparison_periodise_convolution_integrable_of_integrable
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    {f : SpaceTime → ℝ} (hf : Integrable f) (_hfmeas : Measurable f) :
    ∀ z : SpaceTime, Integrable (fun w => periodise ρ ε w * f (z - w)) := by
  have htop : MemLp (periodise ρ ε) ⊤ :=
    constantsComparison_periodise_memLp ρ hρ hε ⊤
  have hone : MemLp f 1 := memLp_one_iff_integrable.mpr hf
  intro z
  have hshift : MemLp (fun w : SpaceTime => f (z - w)) 1 := by
    apply memLp_one_iff_integrable.mpr
    exact integrable_comp_sub_left_spaceTime hf z
  have hmul := htop.integrable_mul hshift
  change Integrable ((fun w => periodise ρ ε w) * (fun w => f (z - w))) at hmul
  exact hmul

private theorem constantsComparison_c1_wick_integrability
    (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Integrable (fun z : SpaceTime => mollifiedKernel ρ ε z ^ 2) ∧
      Integrable (fun z : SpaceTime => hairerMollifiedKernel N ρ ε z ^ 2) := by
  have hmassive := (mollifiedKernel_facts ρ hρ hε).2
  have hmassiveSq := (constants_finite ρ hρ ⟨hε, hε1⟩).2.2.2.2.2.2.1
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
  refine ⟨hmassiveSq, ?_⟩
  exact hsq.congr (Eventually.of_forall fun z => by simp [pow_two])

/-- The finite first-constant comparison limit, defined without a mollifier. -/
def constantsComparison_wickLimit (N : ℕ) : ℝ :=
  ∫ z, constantsComparisonR N z * (massiveHeatKernel z + hairerKernelTorus N z)

/-- The first-constant difference converges to its explicit mollifier-independent limit. -/
theorem constantsComparison_wickLimit_tendsto
    (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) :
    Tendsto (fun ε : ℝ => wickConstant ρ ε - hairerWickConstant N ρ ε)
      (𝓝[>] 0) (𝓝 (constantsComparison_wickLimit N)) := by
  let R : SpaceTime → ℝ := constantsComparisonR N
  let P : SpaceTime → ℝ := fun z => massiveHeatKernel z + hairerKernelTorus N z
  have hRm : Measurable R := measurable_massiveHeatKernel.sub
    (measurable_constantsComparison_hairerKernelTorus N)
  have hPm : Measurable P := measurable_massiveHeatKernel.add
    (measurable_constantsComparison_hairerKernelTorus N)
  have h := constantsComparison_mollifiedPairing_tendsto ρ hρ hRm hPm
    (constantsComparisonR_memLp_four N)
    (constantsComparison_massivePlusHairer_memLp_fourThirds N) 0
  simp only [zero_add] at h
  change Tendsto _ (𝓝[>] 0) (𝓝 (constantsComparison_wickLimit N)) at h
  apply h.congr'
  have hle : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ≤ 1 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [self_mem_nhdsWithin, hle] with ε hε hε1
  have hconvG := constantsComparison_periodise_convolution_integrable_of_integrable
    ρ hρ hε integrable_massiveHeatKernel measurable_massiveHeatKernel
  have hconvK := constantsComparison_periodise_convolution_integrable_of_integrable
    ρ hρ hε (integrable_constantsComparison_hairerKernelTorus N)
      (measurable_constantsComparison_hairerKernelTorus N)
  have hR_eq : spaceTimeConvolution (periodise ρ ε) R = wickComparisonR N ρ ε := by
    change spaceTimeConvolution (periodise ρ ε)
      (massiveHeatKernel - hairerKernelTorus N) = _
    rw [constantsComparison_convolution_difference_eq ρ massiveHeatKernel
      (hairerKernelTorus N) hconvG hconvK,
      constantsComparison_mollifiedKernel_eq_convolution ρ,
      constantsComparison_hairerMollifiedKernel_eq_convolution N ρ]
    rfl
  have hP_eq : spaceTimeConvolution (periodise ρ ε) P = wickComparisonP N ρ ε := by
    change spaceTimeConvolution (periodise ρ ε)
      (massiveHeatKernel + hairerKernelTorus N) = _
    rw [constantsComparison_convolution_add_eq ρ massiveHeatKernel
      (hairerKernelTorus N) hconvG hconvK,
      constantsComparison_mollifiedKernel_eq_convolution ρ,
      constantsComparison_hairerMollifiedKernel_eq_convolution N ρ]
    rfl
  rw [hR_eq, hP_eq]
  obtain ⟨hGint, hKint⟩ := constantsComparison_c1_wick_integrability N ρ hρ hε hε1
  exact (wickConstant_sub_hairerWickConstant_integrand N ρ ε hGint hKint).symm

end RegularityStructures.Phi43

end
