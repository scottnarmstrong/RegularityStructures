/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.TaylorKernel
public import Mathlib.Analysis.Convolution

/-!
# Derivatives of the pairing of a locally integrable function with a shifted smooth kernel

For `Λ` locally integrable and `g` smooth with compact support, the function
`G z = ∫ Λ w g(z - w) dw` is smooth and its directional derivatives are obtained by
differentiating the kernel: `D_{d₁} ⋯ D_{dₙ} G z = ∫ Λ w (D_{d₁} ⋯ D_{dₙ} g)(z - w) dw`
(`lineIter_integral_mul_sub`).

Source: [Hai14] = arXiv:1303.5113v4, proof of Lemma 5.18 (derivatives of the regularised pairing).
-/

public section

open MeasureTheory
open scoped ContDiff Convolution

namespace RegularityStructures

variable {Λ g : ParabolicSpace → ℝ}

private instance : (volume : Measure ParabolicSpace).IsAddLeftInvariant := by
  rw [Measure.volume_eq_prod]; infer_instance

theorem integral_mul_sub_eq_convolution (Λ g : ParabolicSpace → ℝ) :
    (fun z => ∫ w, Λ w * g (z - w)) =
      Λ ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g := by
  funext z
  simp [MeasureTheory.convolution]

theorem contDiff_integral_mul_sub (hΛ : LocallyIntegrable Λ) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) : ContDiff ℝ ∞ (fun z => ∫ w, Λ w * g (z - w)) := by
  rw [integral_mul_sub_eq_convolution]
  exact hc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hΛ hg

theorem dirDeriv_integral_mul_sub (hΛ : LocallyIntegrable Λ) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (e : ParabolicSpace) :
    dirDeriv e (fun z => ∫ w, Λ w * g (z - w)) =
      fun z => ∫ w, Λ w * dirDeriv e g (z - w) := by
  funext z
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by exact_mod_cast le_top)
  have h := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hΛ hg1 z
  have hd : fderiv ℝ (Λ ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g) z =
      (Λ ⋆[(ContinuousLinearMap.mul ℝ ℝ).precompR ParabolicSpace, volume] fderiv ℝ g) z :=
    h.fderiv
  have hcs : HasCompactSupport (fderiv ℝ g) := hc.fderiv ℝ
  have hcont : Continuous (fderiv ℝ g) := (hg.continuous_fderiv (by simp))
  have hex := hcs.convolutionExists_right ((ContinuousLinearMap.mul ℝ ℝ).precompR ParabolicSpace)
    hΛ hcont z
  unfold dirDeriv
  rw [integral_mul_sub_eq_convolution, hd]
  simp only [MeasureTheory.convolution]
  rw [ContinuousLinearMap.integral_apply hex]
  simp [ContinuousLinearMap.precompR_apply]

theorem lineIter_integral_mul_sub (hΛ : LocallyIntegrable Λ) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (L : List ParabolicSpace) :
    lineIter L (fun z => ∫ w, Λ w * g (z - w)) =
      fun z => ∫ w, Λ w * lineIter L g (z - w) := by
  induction L with
  | nil => rfl
  | cons d L ih =>
    rw [lineIter_cons, ih, dirDeriv_integral_mul_sub hΛ (contDiff_lineIter hg L)
      (hasCompactSupport_lineIter hc L) d]
    rfl

theorem integrable_integral_mul_sub (hΛ : LocallyIntegrable Λ) (hg : Continuous g)
    (hc : HasCompactSupport g) (z : ParabolicSpace) :
    Integrable (fun w => Λ w * g (z - w)) := by
  have h := hc.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ) hΛ hg z
  simpa [MeasureTheory.ConvolutionExistsAt] using h

/-- The regularised pairing with a Taylor-remainder kernel is the Taylor remainder of the
regularised pairing with the kernel. -/
theorem integral_mul_taylorProfile (hΛ : LocallyIntegrable Λ) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (σ : ℝ) (x y : ParabolicSpace) :
    ∫ w, Λ w * taylorProfile g σ (y - x) (x - w) =
      taylorProfile (fun z => ∫ w, Λ w * g (z - w)) σ (y - x) x := by
  have hint : ∀ L : List ParabolicSpace, ∀ z : ParabolicSpace,
      Integrable (fun w => Λ w * lineIter L g (z - w)) := fun L z =>
    integrable_integral_mul_sub hΛ (contDiff_lineIter hg L).continuous
      (hasCompactSupport_lineIter hc L) z
  have h1 : ∀ w, Λ w * taylorProfile g σ (y - x) (x - w) =
      Λ w * g (y - w) - ∑ k ∈ taylorIdx σ,
        (evalParabolic (MvPolynomial.monomial k 1) (y - x) / multiFact k) *
          (Λ w * lineIter (multiDirs k) g (x - w)) := by
    intro w
    unfold taylorProfile
    rw [show x - w + (y - x) = y - w by abel, mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => by ring
  have hA : Integrable (fun w => Λ w * g (y - w)) := hint [] y
  have hB : Integrable (fun w => ∑ k ∈ taylorIdx σ,
      (evalParabolic (MvPolynomial.monomial k 1) (y - x) / multiFact k) *
        (Λ w * lineIter (multiDirs k) g (x - w))) :=
    integrable_finsetSum _ fun k _ => (hint _ x).const_mul _
  simp_rw [h1]
  rw [integral_sub hA hB, integral_finsetSum _ fun k _ => (hint _ x).const_mul _]
  unfold taylorProfile
  simp only [lineIter_integral_mul_sub hΛ hg hc, integral_const_mul]
  rw [show x + (y - x) = y by abel]

end RegularityStructures

end
