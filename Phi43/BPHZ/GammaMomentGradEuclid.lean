/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.CanonicalBridgeKernel
public import RegularityStructures.Analysis.Heat.Schauder.TaylorWord
public import Phi43.BPHZ.GammaMomentGradKernel
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The Euclidean gradient kernel is integrable

`hairerKernelGrad N i = ∑ₙ ∂ᵢ S_n` is a sum of rescalings of the fixed compactly supported profile
`∂ᵢ K₀`; the `L¹` norms of the shells are `(1/2)ⁿ ‖∂ᵢ K₀‖₁`.  Hence `hairerKernelGrad N i` is
integrable on `ℝ⁴`, and its reflection times a continuous function is integrable.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

theorem hasCompactSupport_lineIter_annShellC (N n : ℕ) (i : Fin 3) :
    HasCompactSupport (lineIter [spaceDir i] (annShellC N n)) :=
  hasCompactSupport_lineIter (hasCompactSupport_scaledShell
    (fun _ hz => annKernel0C_eq_zero N hz) n) _

theorem integrable_lineIter_annShellC (N n : ℕ) (i : Fin 3) :
    Integrable (lineIter [spaceDir i] (annShellC N n)) :=
  (contDiff_lineIter (contDiff_annShellC N n) _).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_lineIter_annShellC N n i)

/-- `‖∂ᵢ S_n‖₁ = (1/2)ⁿ ‖∂ᵢ K₀‖₁`. -/
theorem integral_abs_lineIter_annShellC (N : ℕ) (i : Fin 3) (n : ℕ) :
    (∫ w, |lineIter [spaceDir i] (annShellC N n) w|) =
      (1 / 2 : ℝ) ^ n * ∫ w, |lineIter [spaceDir i] (annKernel0C N) w| := by
  have hh := integral_abs_word_scaledShell (contDiff_annKernel0C N) [i.succ] n
  have hw : indexWeight [i.succ] = 1 := by
    fin_cases i <;> simp [indexWeight_cons, indexWeight_nil, parabolicWeight]
  simp only [List.map_cons, List.map_nil, coordDir_succ, hw, pow_one] at hh
  change (∫ w, |lineIter [spaceDir i] (scaledShell (annKernel0C N) n) w|) = _
  rw [hh]
  have hfactor : (2 : ℝ) ^ n * (((2 : ℝ) ^ n)⁻¹ ^ 2) = (1 / 2 : ℝ) ^ n := by
    simp only [one_div, inv_pow]
    field_simp
  calc
    _ = ((2 : ℝ) ^ n * (((2 : ℝ) ^ n)⁻¹ ^ 2)) *
        (∫ w, |lineIter [spaceDir i] (annKernel0C N) w|) := by ring
    _ = _ := by rw [hfactor]

theorem summable_integral_norm_lineIter_annShellC (N : ℕ) (i : Fin 3) :
    Summable (fun n : ℕ => ∫ w, ‖lineIter [spaceDir i] (annShellC N n) w‖) := by
  have h : ∀ n : ℕ, ∫ w, ‖lineIter [spaceDir i] (annShellC N n) w‖ =
      (∫ w, |lineIter [spaceDir i] (annKernel0C N) w|) * (1 / 2 : ℝ) ^ n := by
    intro n
    simp only [Real.norm_eq_abs]
    rw [integral_abs_lineIter_annShellC, mul_comm]
  simp_rw [h]
  exact (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left _

/-- The Euclidean gradient kernel is integrable. -/
theorem integrable_hairerKernelGrad (N : ℕ) (i : Fin 3) : Integrable (hairerKernelGrad N i) := by
  have hm : Measurable (hairerKernelGrad N i) := hairerKernelGrad_measurable N i
  have hs := summable_integral_norm_lineIter_annShellC N i
  have hn : (∑' n : ℕ, ∫⁻ w, ‖lineIter [spaceDir i] (annShellC N n) w‖ₑ) ≠ ⊤ := by
    have he (n : ℕ) : (∫⁻ w, ‖lineIter [spaceDir i] (annShellC N n) w‖ₑ) =
        ‖∫ w, ‖lineIter [spaceDir i] (annShellC N n) w‖‖ₑ := by
      rw [← ofReal_integral_norm_eq_lintegral_enorm (integrable_lineIter_annShellC N n i)]
      rw [Real.enorm_eq_ofReal (integral_nonneg (fun _ => norm_nonneg _))]
    simp_rw [he]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 (NNReal.summable_coe.1 hs.abs)
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc
    (∫⁻ w, ‖hairerKernelGrad N i w‖ₑ)
        ≤ ∫⁻ w, ∑' n : ℕ, ‖lineIter [spaceDir i] (annShellC N n) w‖ₑ :=
      lintegral_mono fun w => enorm_tsum_le_tsum_enorm
    _ = ∑' n : ℕ, ∫⁻ w, ‖lineIter [spaceDir i] (annShellC N n) w‖ₑ :=
      lintegral_tsum fun n =>
        (contDiff_lineIter (contDiff_annShellC N n) _).continuous.measurable.enorm.aemeasurable
    _ < ⊤ := lt_top_iff_ne_top.2 hn

/-- The reflected gradient kernel is integrable. -/
theorem integrable_hairerKernelGrad_sub (N : ℕ) (i : Fin 3) (y : ParabolicSpace) :
    Integrable (fun w => hairerKernelGrad N i (y - w)) := by
  have : (volume : Measure ParabolicSpace).IsAddLeftInvariant := by
    rw [Measure.volume_eq_prod]; infer_instance
  have : (volume : Measure ParabolicSpace).IsNegInvariant := by
    rw [Measure.volume_eq_prod]
    have : (volume.prod volume : Measure ParabolicSpace).IsAddHaarMeasure := inferInstance
    have : (volume.prod volume : Measure ParabolicSpace).Regular := inferInstance
    infer_instance
  exact (integrable_hairerKernelGrad N i).comp_sub_left y

/-- The reflected gradient kernel times a continuous function is integrable on `ℝ⁴`. -/
theorem integrable_hairerKernelGrad_sub_mul_continuous (N : ℕ) (i : Fin 3) (y : ParabolicSpace)
    {f : ParabolicSpace → ℝ} (hf : Continuous f) :
    Integrable (fun w => hairerKernelGrad N i (y - w) * f w) := by
  have hcpt : IsCompact ((fun z : ParabolicSpace => y - z) ''
      {z : ParabolicSpace | parabolicNorm z ≤ 1}) :=
    (isCompact_parabolicNorm_le 1).image (continuous_const.sub continuous_id)
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn hf.continuousOn
  refine ((integrable_hairerKernelGrad_sub N i y).abs.mul_const C).mono' ?_
    (Filter.Eventually.of_forall fun w => ?_)
  · exact (((hairerKernelGrad_measurable N i).comp (measurable_const.sub measurable_id)).mul
      hf.measurable).aestronglyMeasurable
  · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    by_cases hw : 1 < parabolicNorm (y - w)
    · rw [hairerKernelGrad_eq_zero_of_one_lt N i hw]
      simp
    · refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have hmem : w ∈ (fun z : ParabolicSpace => y - z) ''
          {z : ParabolicSpace | parabolicNorm z ≤ 1} :=
        ⟨y - w, not_lt.1 hw, by simp⟩
      simpa using hC w hmem

end RegularityStructures.Phi43

end
