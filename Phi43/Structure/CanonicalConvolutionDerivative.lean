/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalSmoothConvolution
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiation under the actual causal convolution

Hairer [Hai14, Proposition 8.27, (8.25)]. Compact support of the causal
kernel provides local domination of the differentiated integrand. This
identity is a quantitative bridge from derivative bounds on the noise;
no analytic model-bound data are assumed.
-/

public noncomputable section

open MeasureTheory Set Filter
open scoped Topology Pointwise

namespace RegularityStructures.Phi43

local instance : (volume : Measure ParabolicSpace).IsAddLeftInvariant := by
  rw [Measure.volume_eq_prod]; infer_instance

local instance : (volume : Measure ParabolicSpace).IsNegInvariant := by
  rw [Measure.volume_eq_prod]
  have : (volume.prod volume : Measure ParabolicSpace).IsAddHaarMeasure := inferInstance
  have : (volume.prod volume : Measure ParabolicSpace).Regular := inferInstance
  infer_instance

open scoped ContDiff in
/-- The derivative of the genuine singular-kernel convolution is obtained
by differentiating its smooth input, without any growth premise. -/
theorem hasFDerivAt_hairerConvolution (N : ℕ) {f : ParabolicSpace → ℝ}
    (hf : ContDiff ℝ ∞ f) (z : ParabolicSpace) :
    HasFDerivAt (hairerConvolution N f)
      (∫ w, hairerKernel N w • fderiv ℝ f (z - w)) z := by
  have hfd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  have hc := canonicalHairerKernel_hasCompactSupport N
  have hi := canonicalHairerKernel_integrable N
  let S := Metric.closedBall z 1 + -tsupport (hairerKernel N)
  have hS : IsCompact S := (isCompact_closedBall z 1).add hc.isCompact.neg
  obtain ⟨D, hD⟩ := hS.exists_bound_of_continuousOn hfd.continuousOn
  have hd (x w : ParabolicSpace) (hx : x ∈ Metric.closedBall z 1)
      (hw : hairerKernel N w ≠ 0) : ‖fderiv ℝ f (x - w)‖ ≤ max D 0 := by
    apply (hD (x - w) ?_).trans (le_max_left _ _)
    refine Set.mem_add.2 ⟨x, hx, -w, ?_, by abel⟩
    simpa only [Set.mem_neg, neg_neg] using
      (subset_tsupport (hairerKernel N) hw : w ∈ tsupport (hairerKernel N))
  have hint (x : ParabolicSpace) :
      Integrable (fun w => hairerKernel N w * f (x - w)) :=
    hc.convolutionExists_left_of_continuous_right (ContinuousLinearMap.mul ℝ ℝ)
      hi.locallyIntegrable hf.continuous x
  have hmeas (x : ParabolicSpace) :
      AEStronglyMeasurable (fun w => hairerKernel N w • fderiv ℝ f (x - w)) :=
    hi.aestronglyMeasurable.smul
      ((hfd.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  have he : hairerConvolution N f =
      fun x => ∫ w, hairerKernel N w * f (x - w) := by
    rw [hairerConvolution_eq_convolution]
    rfl
  rw [he]
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (Metric.closedBall_mem_nhds z (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall fun x => (hint x).aestronglyMeasurable) (hint z) (hmeas z)
    (bound := fun w => |hairerKernel N w| * max D 0)
  · exact Eventually.of_forall fun w x hx => by
      rw [norm_smul, Real.norm_eq_abs]
      by_cases hw : hairerKernel N w = 0
      · rw [hw]; simp only [abs_zero, zero_mul, le_refl]
      · exact mul_le_mul_of_nonneg_left (hd x w hx hw) (abs_nonneg _)
  · exact hi.abs.mul_const _
  · exact Eventually.of_forall fun w x _ => by
      have h : HasFDerivAt (fun x => f (x - w)) (fderiv ℝ f (x - w)) x := by
        simpa using! (hf.differentiable (by simp) (x - w)).hasFDerivAt.comp x
          ((hasFDerivAt_id x).sub (hasFDerivAt_const w x))
      simpa only [Pi.smul_apply, smul_eq_mul] using! h.const_smul (hairerKernel N w)

open scoped ContDiff in
/-- Operator-valued convolution identity for the derivative. -/
theorem fderiv_hairerConvolution (N : ℕ) {f : ParabolicSpace → ℝ}
    (hf : ContDiff ℝ ∞ f) (z : ParabolicSpace) :
    fderiv ℝ (hairerConvolution N f) z =
      ∫ w, hairerKernel N w • fderiv ℝ f (z - w) :=
  (hasFDerivAt_hairerConvolution N hf z).fderiv

end RegularityStructures.Phi43

end
