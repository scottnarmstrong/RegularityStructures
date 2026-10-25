/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalSmoothConvolution

/-!
# Linearity of actual causal convolution on continuous functions

Compact support and integrability of the actual kernel ensure the Bochner
integrals exist. Constant Taylor differences cancel constant sources even
without using vanishing moments [Hai14, (5.12), (8.20)].
-/

public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

theorem hairerConvolution_sub_continuous (N : ℕ) {f g : ParabolicSpace → ℝ}
    (hf : Continuous f) (hg : Continuous g) (z : ParabolicSpace) :
    hairerConvolution N (fun w => f w - g w) z =
      hairerConvolution N f z - hairerConvolution N g z := by
  simp only [hairerConvolution_eq_convolution, convolution_def, ContinuousLinearMap.mul_apply']
  simp only [mul_sub]
  exact integral_sub
    ((canonicalHairerKernel_hasCompactSupport N).convolutionExists_left_of_continuous_right
      (ContinuousLinearMap.mul ℝ ℝ) (canonicalHairerKernel_integrable N).locallyIntegrable hf z)
    ((canonicalHairerKernel_hasCompactSupport N).convolutionExists_left_of_continuous_right
      (ContinuousLinearMap.mul ℝ ℝ) (canonicalHairerKernel_integrable N).locallyIntegrable hg z)

theorem hairerConvolution_mul_const (N : ℕ) (f : ParabolicSpace → ℝ) (c : ℝ)
    (z : ParabolicSpace) :
    hairerConvolution N (fun w => c * f w) z = c * hairerConvolution N f z := by
  simp only [hairerConvolution_eq_convolution, convolution_def, ContinuousLinearMap.mul_apply']
  simp only [mul_left_comm _ c]
  exact integral_const_mul _ _

theorem hairerConvolution_const_value (N : ℕ) (c : ℝ) (z : ParabolicSpace) :
    hairerConvolution N (fun _ => c) z = (∫ w, hairerKernel N w) * c := by
  simp only [hairerConvolution_eq_convolution, convolution_def, ContinuousLinearMap.mul_apply']
  exact integral_mul_const _ _

end RegularityStructures.Phi43

end
