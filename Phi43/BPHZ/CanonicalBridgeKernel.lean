/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalKernelHairer
public import Phi43.Stochastic.ConstantsComparisonKernelLp
public import RegularityStructures.Analysis.Heat.Schauder.DerivativeScaling
public import RegularityStructures.Analysis.Heat.Decomposition.Support
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The Hairer kernel on `ℝ⁴` is integrable with compact support

This is the Euclidean input of the bridge between the concrete canonical data on
`ParabolicSpace = ℝ⁴` and the tree fields on `ℝ × T³`.  The kernel `hairerKernel N` is the sum of its
causal shells, each of which is a rescaling of a fixed smooth compactly supported function, so the
`L¹` norms of the shells are summable (geometric).  Consequently `hairerKernel N` is integrable, it
vanishes outside the unit parabolic ball, and its convolution with a continuous function exists.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem bridge_shell_integrable (N n : ℕ) : Integrable (annShellC N n) :=
  (contDiff_annShellC N n).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_scaledShell (fun _ hz => annKernel0C_eq_zero N hz) n)

private theorem bridge_shell_support_unit (N n : ℕ) {w : ParabolicSpace}
    (hw : 1 < parabolicNorm w) : annShellC N n w = 0 := by
  apply annShellC_eq_zero
  exact lt_of_le_of_lt (pow_le_one₀ (by norm_num : 0 ≤ (2 : ℝ)⁻¹)
    (by norm_num : (2 : ℝ)⁻¹ ≤ 1)) hw

private theorem bridge_shell_abs_integral (N n : ℕ) :
    ∫ w, |annShellC N n w| = (1 / 4 : ℝ) ^ n * ∫ w, |annKernel0C N w| := by
  change (∫ w, |scaledShell (annKernel0C N) n w|) = _
  rw [integral_abs_scaledShell]
  congr 1
  rw [inv_pow, ← pow_mul, Nat.mul_comm n 2, pow_mul, ← inv_pow]
  norm_num

private theorem bridge_shell_summable (N : ℕ) :
    Summable (fun n : ℕ => ∫ w, ‖annShellC N n w‖) := by
  have h : ∀ n : ℕ, ∫ w, ‖annShellC N n w‖ = (∫ w, |annKernel0C N w|) * (1 / 4 : ℝ) ^ n := by
    intro n
    simp only [Real.norm_eq_abs]
    rw [bridge_shell_abs_integral, mul_comm]
  simp_rw [h]
  exact (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)).mul_left _

/-- The Hairer kernel on `ℝ⁴` vanishes outside the unit parabolic ball. -/
theorem hairerKernel_eq_zero_of_one_lt_parabolicNorm (N : ℕ) {w : ParabolicSpace}
    (hw : 1 < parabolicNorm w) : hairerKernel N w = 0 := by
  simp [hairerKernel, bridge_shell_support_unit N _ hw]

/-- The Hairer kernel on `ℝ⁴` is integrable. -/
theorem integrable_hairerKernel (N : ℕ) : Integrable (hairerKernel N) := by
  have hm : Measurable (hairerKernel N) :=
    Measurable.tsum fun n => (contDiff_annShellC N n).continuous.measurable
  have hs := bridge_shell_summable N
  have hn : (∑' n : ℕ, ∫⁻ w, ‖annShellC N n w‖ₑ) ≠ ⊤ := by
    have he (n : ℕ) : (∫⁻ w, ‖annShellC N n w‖ₑ) =
        ‖∫ w, ‖annShellC N n w‖‖ₑ := by
      rw [← ofReal_integral_norm_eq_lintegral_enorm (bridge_shell_integrable N n)]
      rw [Real.enorm_eq_ofReal (integral_nonneg (fun _ => norm_nonneg _))]
    simp_rw [he]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 (NNReal.summable_coe.1 hs.abs)
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc
    (∫⁻ w, ‖hairerKernel N w‖ₑ) ≤ ∫⁻ w, ∑' n : ℕ, ‖annShellC N n w‖ₑ :=
      lintegral_mono fun w => enorm_tsum_le_tsum_enorm
    _ = ∑' n : ℕ, ∫⁻ w, ‖annShellC N n w‖ₑ :=
      lintegral_tsum fun n => (contDiff_annShellC N n).continuous.measurable.enorm.aemeasurable
    _ < ⊤ := lt_top_iff_ne_top.2 hn

/-- The reflected Hairer kernel `w ↦ K(y - w)` on `ℝ⁴` is integrable. -/
theorem integrable_hairerKernel_sub (N : ℕ) (y : ParabolicSpace) :
    Integrable (fun w => hairerKernel N (y - w)) := by
  have : (volume : Measure ParabolicSpace).IsAddLeftInvariant := by
    rw [Measure.volume_eq_prod]; infer_instance
  have : (volume : Measure ParabolicSpace).IsNegInvariant := by
    rw [Measure.volume_eq_prod]
    have : (volume.prod volume : Measure ParabolicSpace).IsAddHaarMeasure := inferInstance
    have : (volume.prod volume : Measure ParabolicSpace).Regular := inferInstance
    infer_instance
  exact (integrable_hairerKernel N).comp_sub_left y

/-- The reflected Hairer kernel times a continuous function is integrable on `ℝ⁴`:
only the compact unit neighbourhood of `y` matters. -/
theorem integrable_hairerKernel_sub_mul_continuous (N : ℕ) (y : ParabolicSpace)
    {f : ParabolicSpace → ℝ} (hf : Continuous f) :
    Integrable (fun w => hairerKernel N (y - w) * f w) := by
  have hcpt : IsCompact ((fun z : ParabolicSpace => y - z) ''
      {z : ParabolicSpace | parabolicNorm z ≤ 1}) :=
    (isCompact_parabolicNorm_le 1).image (continuous_const.sub continuous_id)
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn hf.continuousOn
  refine ((integrable_hairerKernel_sub N y).abs.mul_const C).mono' ?_
    (Filter.Eventually.of_forall fun w => ?_)
  · exact (((measurable_constantsComparison_hairerKernel N).comp (measurable_const.sub measurable_id)).mul
      hf.measurable).aestronglyMeasurable
  · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    by_cases hw : 1 < parabolicNorm (y - w)
    · rw [hairerKernel_eq_zero_of_one_lt_parabolicNorm N hw]
      simp
    · refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have hmem : w ∈ (fun z : ParabolicSpace => y - z) ''
          {z : ParabolicSpace | parabolicNorm z ≤ 1} :=
        ⟨y - w, not_lt.1 hw, by simp⟩
      simpa using hC w hmem

end RegularityStructures.Phi43

end
