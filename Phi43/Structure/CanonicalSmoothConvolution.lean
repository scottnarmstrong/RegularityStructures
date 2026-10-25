/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalSmoothShellBridge
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Tactic.Abel

/-!+# Smooth convolution with the causal Hairer kernel

Hairer [Hai14, Proposition 8.27, (8.25)]: convolution of the compactly
supported singular kernel with a smooth function is smooth. A local
cutoff reduces this to Mathlib's smooth compact-support convolution
theorem. No growth at infinity is required.
-/

public noncomputable section

open MeasureTheory Set Filter
open scoped Topology Convolution

namespace RegularityStructures.Phi43

local instance : (volume : Measure ParabolicSpace).IsAddLeftInvariant := by
  rw [Measure.volume_eq_prod]; infer_instance

local instance : (volume : Measure ParabolicSpace).IsNegInvariant := by
  rw [Measure.volume_eq_prod]
  have : (volume.prod volume : Measure ParabolicSpace).IsAddHaarMeasure := inferInstance
  have : (volume.prod volume : Measure ParabolicSpace).Regular := inferInstance
  infer_instance

/-- The convolution used by the canonical lift is the usual scalar convolution. -/
theorem hairerConvolution_eq_convolution (N : ℕ) (f : ParabolicSpace → ℝ) :
    hairerConvolution N f =
      hairerKernel N ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] f := by
  funext z
  exact (convolution_mul_swap (x := z)).symm

private theorem shifted_parabolic_ball_compact (z : ParabolicSpace) (r : ℝ) :
    IsCompact {y : ParabolicSpace | parabolicNorm (y - z) ≤ r} :=
  (Homeomorph.subRight z).isClosedEmbedding.isCompact_preimage
    (isCompact_parabolicNorm_le r)

open scoped ContDiff in
private theorem smooth_local_cutoff (z : ParabolicSpace) :
    ∃ χ : ParabolicSpace → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      ∀ y, parabolicNorm (y - z) ≤ 2 → χ y = 1 := by
  have hc : Continuous (fun y : ParabolicSpace => parabolicNorm (y - z)) :=
    continuous_parabolicNorm.comp (continuous_id.sub continuous_const)
  obtain ⟨χ, hχ, _, hs, hone⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞))
    (s := {y : ParabolicSpace | parabolicNorm (y - z) < 3})
    (t := {y : ParabolicSpace | parabolicNorm (y - z) ≤ 2})
    (isOpen_lt hc continuous_const)
    (isClosed_le hc continuous_const)
    (show {y : ParabolicSpace | parabolicNorm (y - z) ≤ 2} ⊆
      {y | parabolicNorm (y - z) < 3} from
        fun _ hy => lt_of_le_of_lt hy (by norm_num : (2 : ℝ) < 3))
  refine ⟨χ, hχ, ?_, fun y hy => (hone y).1 hy⟩
  apply HasCompactSupport.intro (shifted_parabolic_ball_compact z 3)
  intro y hy
  change ¬ parabolicNorm (y - z) ≤ 3 at hy
  have hnot : y ∉ Function.support χ := by
    rw [hs]
    exact not_lt_of_ge (le_of_lt (lt_of_not_ge hy))
  exact not_not.1 hnot

open scoped ContDiff in
/-- Smooth input gives a smooth actual kernel convolution, independently
of its temporal growth [Hai14, Proposition 8.27]. -/
theorem contDiff_hairerConvolution (N : ℕ) {f : ParabolicSpace → ℝ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (hairerConvolution N f) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  obtain ⟨χ, hχ, hχc, hone⟩ := smooth_local_cutoff z
  have hsm : ContDiff ℝ ∞ (hairerConvolution N (χ * f)) := by
    rw [hairerConvolution_eq_convolution]
    exact (hχc.mul_right).contDiff_convolution_right
      (ContinuousLinearMap.mul ℝ ℝ) (canonicalHairerKernel_integrable N).locallyIntegrable
      (hχ.mul hf)
  apply hsm.contDiffAt.congr_of_eventuallyEq
  have ho : IsOpen {y : ParabolicSpace | parabolicNorm (y - z) < 1} :=
    isOpen_lt (continuous_parabolicNorm.comp (continuous_id.sub continuous_const))
      continuous_const
  have hz : z ∈ {y : ParabolicSpace | parabolicNorm (y - z) < 1} := by simp
  filter_upwards [ho.mem_nhds hz] with y hy
  simp only [hairerConvolution_eq_convolution, convolution_def, ContinuousLinearMap.mul_apply']
  apply integral_congr_ae
  exact Eventually.of_forall fun w => by
    change hairerKernel N w * f (y - w) = hairerKernel N w * ((χ * f) (y - w))
    by_cases hw : parabolicNorm w ≤ 1
    · have harg : parabolicNorm (y - w - z) ≤ 2 := by
        have he : y - w - z = (y - z) + -w := by abel
        rw [he]
        have hh := parabolicNorm_add_le (y - z) (-w)
        rw [parabolicNorm_neg] at hh
        exact hh.trans (by linarith)
      simp [Pi.mul_apply, hone (y - w) harg]
    · rw [canonicalHairerKernel_eq_zero N (lt_of_not_ge hw)]
      simp only [zero_mul]

end RegularityStructures.Phi43

end
