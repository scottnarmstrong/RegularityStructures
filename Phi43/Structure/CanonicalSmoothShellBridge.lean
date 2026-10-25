/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalKernelHairer
public import RegularityStructures.Analysis.Heat.Schauder.DerivativeScaling
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Normed

/-!+# Convolution by the causal kernel as a sum of shell convolutions

Hairer [Hai14, Lemma 5.5, (8.25)]: the singular kernel used in the
canonical lift is the sum of its causal shells, also after convolution.
The proof uses the summable L¹ shell norms. Only continuity on the compact
unit neighbourhood of the evaluation point is needed; no global growth
or analytic model bounds are assumed.
-/

public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

private theorem shell_integrable (N n : ℕ) : Integrable (annShellC N n) :=
  (contDiff_annShellC N n).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_scaledShell (fun _ hz => annKernel0C_eq_zero N hz) n)

private theorem shell_support_unit (N n : ℕ) {w : ParabolicSpace}
    (hw : 1 < parabolicNorm w) : annShellC N n w = 0 := by
  apply annShellC_eq_zero
  exact lt_of_le_of_lt (pow_le_one₀ (by norm_num : 0 ≤ (2 : ℝ)⁻¹)
    (by norm_num : (2 : ℝ)⁻¹ ≤ 1)) hw

private theorem shell_abs_integral (N n : ℕ) :
    ∫ w, |annShellC N n w| = (1 / 4 : ℝ) ^ n * ∫ w, |annKernel0C N w| := by
  change (∫ w, |scaledShell (annKernel0C N) n w|) = _
  rw [integral_abs_scaledShell]
  congr 1
  rw [inv_pow, ← pow_mul, Nat.mul_comm n 2, pow_mul, ← inv_pow]
  norm_num

/-- Absolute summability of the shell convolutions against a continuous
function. The function is bounded only on a compact neighbourhood of `z`. -/
theorem canonicalShell_summable_integral_norm (N : ℕ)
    {f : ParabolicSpace → ℝ} (hf : Continuous f) (z : ParabolicSpace) :
    Summable (fun n : ℕ => ∫ w, ‖annShellC N n w * f (z - w)‖) := by
  have hfc : Continuous (fun w : ParabolicSpace => f (z - w)) :=
    hf.comp (continuous_const.sub continuous_id)
  obtain ⟨B, hB⟩ := (isCompact_parabolicNorm_le 1).exists_bound_of_continuousOn
    hfc.continuousOn
  have hint (n : ℕ) : Integrable (fun w => annShellC N n w * f (z - w)) :=
    ((contDiff_annShellC N n).continuous.mul
      (hf.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
        ((hasCompactSupport_scaledShell (fun _ hz => annKernel0C_eq_zero N hz) n).mul_right)
  have hbound (n : ℕ) :
      (∫ w, ‖annShellC N n w * f (z - w)‖) ≤
        (max B 0 * ∫ w, |annKernel0C N w|) * (1 / 4 : ℝ) ^ n := by
    calc
      _ ≤ ∫ w, max B 0 * |annShellC N n w| := by
        apply integral_mono (hint n).norm ((shell_integrable N n).abs.const_mul _)
        intro w
        by_cases hw : parabolicNorm w ≤ 1
        · change ‖annShellC N n w * f (z - w)‖ ≤ _
          rw [Real.norm_eq_abs, abs_mul]
          have hb' : |f (z - w)| ≤ B := by
            simpa only [Real.norm_eq_abs] using hB w hw
          have hb : |f (z - w)| ≤ max B 0 := hb'.trans (le_max_left _ _)
          exact (mul_le_mul_of_nonneg_left hb (abs_nonneg _)).trans_eq (mul_comm _ _)
        · simp [shell_support_unit N n (lt_of_not_ge hw)]
      _ = _ := by rw [integral_const_mul, shell_abs_integral]; ring
  exact Summable.of_nonneg_of_le (fun n => integral_nonneg (fun _ => norm_nonneg _))
    hbound ((summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)).mul_left _)

/-- Interchange of the causal shell sum and convolution, with no global
growth hypothesis on the continuous input [Hai14, Lemma 5.5, (8.25)]. -/
theorem hairerConvolution_eq_tsum_shellConvolution (N : ℕ)
    {f : ParabolicSpace → ℝ} (hf : Continuous f) (z : ParabolicSpace) :
    hairerConvolution N f z =
      ∑' n : ℕ, ∫ w, annShellC N n w * f (z - w) := by
  have hint (n : ℕ) : Integrable (fun w => annShellC N n w * f (z - w)) :=
    ((contDiff_annShellC N n).continuous.mul
      (hf.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
        ((hasCompactSupport_scaledShell (fun _ hz => annKernel0C_eq_zero N hz) n).mul_right)
  have hsum := integral_tsum_of_summable_integral_norm hint
    (canonicalShell_summable_integral_norm N hf z)
  have heq : (fun w => ∑' n : ℕ, annShellC N n w * f (z - w)) =
      (fun w => hairerKernel N w * f (z - w)) := by
    funext w
    exact tsum_mul_right
  rw [heq] at hsum
  rw [hairerConvolution]
  have : (volume : Measure ParabolicSpace).IsAddLeftInvariant := by
    rw [Measure.volume_eq_prod]; infer_instance
  have : (volume : Measure ParabolicSpace).IsNegInvariant := by
    rw [Measure.volume_eq_prod]
    have : (volume.prod volume : Measure ParabolicSpace).IsAddHaarMeasure := inferInstance
    have : (volume.prod volume : Measure ParabolicSpace).Regular := inferInstance
    infer_instance
  calc
    _ = ∫ w, hairerKernel N w * f (z - w) := by
      simpa only [sub_sub_cancel] using
        (integral_sub_left_eq_self (fun w => hairerKernel N w * f (z - w)) volume z)
    _ = _ := hsum.symm

end RegularityStructures.Phi43

end

public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

/-- The actual causal kernel is integrable. This is an L¹ consequence of
the shell scaling, without a pointwise singular-kernel estimate. -/
theorem canonicalHairerKernel_integrable (N : ℕ) : Integrable (hairerKernel N) := by
  have hm : Measurable (hairerKernel N) :=
    Measurable.tsum fun n => (contDiff_annShellC N n).continuous.measurable
  have hs : Summable (fun n : ℕ => ∫ w, ‖annShellC N n w‖) := by
    simpa only [mul_one] using
      canonicalShell_summable_integral_norm N (f := fun _ => 1) continuous_const 0
  have hn : (∑' n : ℕ, ∫⁻ w, ‖annShellC N n w‖ₑ) ≠ ⊤ := by
    have he (n : ℕ) : (∫⁻ w, ‖annShellC N n w‖ₑ) =
        ‖∫ w, ‖annShellC N n w‖‖ₑ := by
      rw [← ofReal_integral_norm_eq_lintegral_enorm (shell_integrable N n)]
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

/-- The singular sum retains the unit support of its causal shells. -/
theorem canonicalHairerKernel_eq_zero (N : ℕ) {w : ParabolicSpace}
    (hw : 1 < parabolicNorm w) : hairerKernel N w = 0 := by
  simp [hairerKernel, shell_support_unit N _ hw]

/-- Compact support of the singular sum, although it is not continuous at zero. -/
theorem canonicalHairerKernel_hasCompactSupport (N : ℕ) :
    HasCompactSupport (hairerKernel N) :=
  HasCompactSupport.intro (isCompact_parabolicNorm_le 1)
    (fun _ hw => canonicalHairerKernel_eq_zero N (lt_of_not_ge hw))

end RegularityStructures.Phi43

end
