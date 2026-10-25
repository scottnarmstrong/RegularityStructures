/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalConvolutionDerivative

/-!
# Quantitative derivative growth through causal convolution

The derivative envelope is preserved with an explicit constant depending
only on the input envelope, its exponent, and the actual kernel's L1 norm.
This is an ingredient of Hairer [Hai14, Proposition 8.27] in the
polynomially weighted framework [Hos25, Definition 2.1].
-/

public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

open scoped ContDiff in
/-- A quantitative first-derivative envelope for the actual convolution.
No unspecified compactness constant or analytic model bound occurs. -/
theorem norm_fderiv_hairerConvolution_le (N : ℕ) {f : ParabolicSpace → ℝ}
    (hf : ContDiff ℝ ∞ f) (C : ℝ) (p : ℕ)
    (hder : ∀ z, ‖fderiv ℝ f z‖ ≤ C * (1 + parabolicNorm z) ^ p)
    (z : ParabolicSpace) :
    ‖fderiv ℝ (hairerConvolution N f) z‖ ≤
      (∫ w, |hairerKernel N w|) * C * 2 ^ p * (1 + parabolicNorm z) ^ p := by
  have hC : 0 ≤ C := by
    have h := (norm_nonneg (fderiv ℝ f 0)).trans (hder 0)
    simpa only [parabolicNorm_zero, add_zero, one_pow, mul_one] using h
  have hpow (w : ParabolicSpace) (hw : parabolicNorm w ≤ 1) :
      (1 + parabolicNorm (z - w)) ^ p ≤ 2 ^ p * (1 + parabolicNorm z) ^ p := by
    have hn : 1 + parabolicNorm (z - w) ≤ 2 * (1 + parabolicNorm z) := by
      have hh := parabolicNorm_add_le z (-w)
      rw [parabolicNorm_neg, ← sub_eq_add_neg] at hh
      linarith [parabolicNorm_nonneg z]
    simpa only [mul_pow] using
      pow_le_pow_left₀ (by linarith [parabolicNorm_nonneg (z - w)]) hn p
  rw [fderiv_hairerConvolution N hf z]
  have hdom (w : ParabolicSpace) :
      ‖hairerKernel N w • fderiv ℝ f (z - w)‖ ≤
        |hairerKernel N w| * (C * 2 ^ p * (1 + parabolicNorm z) ^ p) := by
    rw [norm_smul, Real.norm_eq_abs]
    by_cases hw : parabolicNorm w ≤ 1
    · apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact (hder (z - w)).trans
        ((mul_le_mul_of_nonneg_left (hpow w hw) hC).trans_eq (by ring))
    · rw [canonicalHairerKernel_eq_zero N (lt_of_not_ge hw)]
      simp only [abs_zero, zero_mul, le_refl]
  calc
    _ ≤ ∫ w, |hairerKernel N w| * (C * 2 ^ p * (1 + parabolicNorm z) ^ p) :=
      norm_integral_le_of_norm_le ((canonicalHairerKernel_integrable N).abs.mul_const _)
        (Filter.Eventually.of_forall hdom)
    _ = _ := by rw [integral_mul_const]; ring

end RegularityStructures.Phi43

end
