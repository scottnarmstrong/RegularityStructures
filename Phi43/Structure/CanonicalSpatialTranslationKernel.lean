/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalSmoothCharacters
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Tactic.Abel

/-!
# Translation symmetry of the actual causal convolution Taylor data

Hairer [Hai14, Section 8.2, Proposition 8.27], an ingredient of the
periodicity of the canonical model. Kernel convolution and
its genuine spatial Taylor derivatives preserve a period of the input.
-/

public noncomputable section

open MeasureTheory
open scoped Convolution

namespace RegularityStructures.Phi43

/-- Actual kernel convolution preserves every additive period of its input. -/
theorem hairerConvolution_translate_of_periodic (N : ℕ) (f : ParabolicSpace → ℝ)
    (a : ParabolicSpace) (hf : ∀ z, f (z + a) = f z) (z : ParabolicSpace) :
    hairerConvolution N f (z + a) = hairerConvolution N f z := by
  rw [hairerConvolution_eq_convolution]
  simp only [convolution_def, ContinuousLinearMap.mul_apply']
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun w => by
    change hairerKernel N w * f (z + a - w) = hairerKernel N w * f (z - w)
    rw [show z + a - w = (z - w) + a by abel, hf]

open scoped ContDiff in
/-- Genuine spatial Taylor derivatives of the convolution preserve the same
period, rather than being independent periodicity data. -/
theorem hairerSpatialGradient_translate_of_periodic (N : ℕ) {f : ParabolicSpace → ℝ}
    (hfs : ContDiff ℝ ∞ f) (a : ParabolicSpace) (hf : ∀ z, f (z + a) = f z)
    (i : Fin 3) (z : ParabolicSpace) :
    hairerSpatialGradient N f i (z + a) = hairerSpatialGradient N f i z := by
  have hd := (contDiff_hairerConvolution N hfs).differentiable (by simp)
  have he : (fun w => hairerConvolution N f (w + a)) = hairerConvolution N f :=
    funext (hairerConvolution_translate_of_periodic N f a hf)
  have hh := (hd (z + a)).hasFDerivAt.comp z ((hasFDerivAt_id z).add_const a)
  have hder : fderiv ℝ (fun w => hairerConvolution N f (w + a)) z =
      fderiv ℝ (hairerConvolution N f) (z + a) := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using! hh.fderiv
  rw [he] at hder
  rw [hairerSpatialGradient_eq_fderiv N hfs, hairerSpatialGradient_eq_fderiv N hfs,
    ← hder]

end RegularityStructures.Phi43

end
