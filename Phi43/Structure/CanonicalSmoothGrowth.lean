/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalSmoothConvolution
public import RegularityStructures.Abstract.Integration.PolyPairing.Limit
public import RegularityStructures.Abstract.Integration.Realising.Reg
import Mathlib.Tactic.Ring

/-!+# Growth of smooth canonical convolutions

Polynomial growth is preserved by the actual compactly supported causal
kernel. This supplies the tail integrability needed by the whole-space
auxiliary semigroup, without assuming model bounds. The compact-test
pairing agrees with the ordinary function integral, also for negative
homogeneities [Hai14, Proposition 8.27; Remark 5.10].
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped Convolution

namespace RegularityStructures.Phi43

/-- Products of polynomially bounded functions remain polynomially bounded. -/
theorem canonicalPolyBounded_mul {f g : ParabolicSpace → ℝ}
    (hf : PolyBounded f) (hg : PolyBounded g) : PolyBounded (f * g) := by
  obtain ⟨hfm, B, n, hB⟩ := hf
  obtain ⟨hgm, C, m, hC⟩ := hg
  have hB0 := nonneg_of_bound hB
  refine ⟨hfm.mul hgm, B * C, n + m, fun z => ?_⟩
  change |f z * g z| ≤ _
  rw [abs_mul, pow_add]
  calc
    _ ≤ (B * (1 + parabolicNorm z) ^ n) * (C * (1 + parabolicNorm z) ^ m) :=
      mul_le_mul (hB z) (hC z) (abs_nonneg _)
        (mul_nonneg hB0 (pow_nonneg (by linarith [parabolicNorm_nonneg z]) _))
    _ = _ := by ring

open scoped ContDiff in
/-- Causal convolution preserves polynomial growth. Its constant depends
only on the input growth bound, exponent and the L¹ norm of the kernel. -/
theorem polyBounded_hairerConvolution (N : ℕ) {f : ParabolicSpace → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfg : PolyBounded f) :
    PolyBounded (hairerConvolution N f) := by
  obtain ⟨_, B, n, hB⟩ := hfg
  have hB0 := nonneg_of_bound hB
  refine ⟨(contDiff_hairerConvolution N hf).continuous.measurable,
    (∫ w, |hairerKernel N w|) * B * 2 ^ n, n, fun z => ?_⟩
  rw [hairerConvolution_eq_convolution, convolution_def]
  change |∫ w, hairerKernel N w * f (z - w)| ≤ _
  have hint : Integrable (fun w => hairerKernel N w * f (z - w)) :=
    (canonicalHairerKernel_hasCompactSupport N).convolutionExists_left_of_continuous_right
      (ContinuousLinearMap.mul ℝ ℝ) (canonicalHairerKernel_integrable N).locallyIntegrable
      hf.continuous z
  calc
    _ ≤ ∫ w, |hairerKernel N w * f (z - w)| := abs_integral_le_integral_abs
    _ ≤ ∫ w, |hairerKernel N w| * (B * 2 ^ n * (1 + parabolicNorm z) ^ n) := by
      apply integral_mono hint.abs ((canonicalHairerKernel_integrable N).abs.mul_const _)
      intro w
      change |hairerKernel N w * f (z - w)| ≤ _
      by_cases hw : parabolicNorm w ≤ 1
      · have hn : 1 + parabolicNorm (z - w) ≤ 2 * (1 + parabolicNorm z) := by
          have hh := parabolicNorm_add_le z (-w)
          rw [parabolicNorm_neg, ← sub_eq_add_neg] at hh
          linarith [parabolicNorm_nonneg z]
        have hp : (1 + parabolicNorm (z - w)) ^ n ≤
            2 ^ n * (1 + parabolicNorm z) ^ n := by
          simpa only [mul_pow] using
            pow_le_pow_left₀ (by linarith [parabolicNorm_nonneg (z - w)]) hn n
        rw [abs_mul]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact (hB (z - w)).trans ((mul_le_mul_of_nonneg_left hp hB0).trans_eq (by ring))
      · simp only [canonicalHairerKernel_eq_zero N (lt_of_not_ge hw), zero_mul, abs_zero,
          le_refl]
    _ = _ := by rw [integral_mul_const]; ring

/-- A smooth polynomially growing input defines a genuine Q-distribution. -/
def canonicalSmoothReg (f : ParabolicSpace → ℝ) (hf : PolyBounded f) :
    parabolicSemigroup.distributions :=
  ⟨fun t z => if 0 < t then parabolicSemigroup.apply t f z else 0,
    mem_distributions_ite_apply hf⟩

/-- Compact-test pairing for the function-valued canonical building blocks;
there is no lower homogeneity restriction on this identity. -/
theorem canonicalSmoothReg_pairing {f φ : ParabolicSpace → ℝ}
    (hf : Continuous f) (hfg : PolyBounded f)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    parabolicSemigroup.pairing (canonicalSmoothReg f hfg) φ = ∫ z, f z * φ z := by
  obtain ⟨_, B, n, hB⟩ := hfg
  apply pairing_eq_integral_of_bound hf hB hφ hφc
  intro s hs
  funext z
  simp only [canonicalSmoothReg, hs, ite_true]

end RegularityStructures.Phi43

end
