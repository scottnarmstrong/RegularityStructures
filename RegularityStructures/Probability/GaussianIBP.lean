/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.WhiteNoise
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Gaussian integration by parts

This file proves the one-dimensional standard-Gaussian identity. The density calculation is the
finite-dimensional instance of the Gaussian integration-by-parts input used in [HS23, Definition
2.20 and Remark 2.22].

The growth and Lebesgue-integrability assumptions are explicit theorem hypotheses. The latter are
exactly the hypotheses consumed by Mathlib's integration-by-parts theorem.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

end

public section

open MeasureTheory ProbabilityTheory Real

namespace RegularityStructures

private lemma hasDerivAt_gaussianPDFReal_zero_one (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  rw [gaussianPDFReal_def]
  have harg : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-x) x := by
    convert ((hasDerivAt_id x).pow 2).neg.div_const (2 : ℝ) using 1
    · norm_num
    · norm_num
      ring
  have hexp : HasDerivAt (fun y : ℝ => rexp (-y ^ 2 / 2))
      (rexp (-x ^ 2 / 2) * (-x)) x :=
    (Real.hasDerivAt_exp _).comp x harg
  have hconst : HasDerivAt (fun _ : ℝ => (√(2 * π))⁻¹) 0 x :=
    hasDerivAt_const x _
  convert hconst.mul hexp using 1
  · funext y
    congr 1
    · norm_num
    · congr 1
      simp only [NNReal.coe_one, mul_one]
      ring_nf
  · simp only [NNReal.coe_one, mul_one]
    ring_nf

theorem gaussian_integration_by_parts_one_dimensional {f : ℝ → ℝ}
    (hcont : ContDiff ℝ 1 f)
    (_hgrowth : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ x : ℝ, |f x| + ‖fderiv ℝ f x‖ ≤ C * (1 + ‖x‖) ^ N)
    (hint_f : Integrable (fun x : ℝ => f x * gaussianPDFReal 0 1 x))
    (hint_deriv : Integrable (fun x : ℝ => fderiv ℝ f x 1 * gaussianPDFReal 0 1 x))
    (hint_x : Integrable (fun x : ℝ => x * f x * gaussianPDFReal 0 1 x)) :
    ∫ x, x * f x ∂(gaussianReal 0 1) =
      ∫ x, fderiv ℝ f x 1 ∂(gaussianReal 0 1) := by
  have hderiv (x : ℝ) : fderiv ℝ (gaussianPDFReal 0 1) x 1 =
      -x * gaussianPDFReal 0 1 x := by
    rw [fderiv_apply_one_eq_deriv, (hasDerivAt_gaussianPDFReal_zero_one x).deriv]
  have hparts := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure ℝ))
    (hf'g := hint_deriv)
    (hfg' := by
      refine hint_x.neg.congr ?_
      filter_upwards [] with x
      rw [hderiv]
      change -(x * f x * gaussianPDFReal 0 1 x) =
        f x * (-x * gaussianPDFReal 0 1 x)
      ring)
    (hfg := hint_f)
    (hf := fun x _ => hcont.contDiffAt.differentiableAt_one)
    (hg := fun x _ => (hasDerivAt_gaussianPDFReal_zero_one x).differentiableAt)
    (v := (1 : ℝ)) (f := f) (g := gaussianPDFReal 0 1)
  rw [integral_gaussianReal_eq_integral_smul
    (f := fun x : ℝ => x * f x) (μ := 0) (v := 1) (by norm_num)]
  rw [integral_gaussianReal_eq_integral_smul
    (f := fun x : ℝ => fderiv ℝ f x 1) (μ := 0) (v := 1) (by norm_num)]
  simp only [smul_eq_mul]
  have hparts' :
      ∫ x, f x * (-x * gaussianPDFReal 0 1 x) =
        -∫ x, fderiv ℝ f x 1 * gaussianPDFReal 0 1 x := by
    convert hparts using 1
    · congr 1
      funext x
      rw [hderiv]
  calc
    ∫ x, gaussianPDFReal 0 1 x * (x * f x) =
        -∫ x, f x * (-x * gaussianPDFReal 0 1 x) := by
      rw [← integral_neg]
      congr 1
      funext x
      ring
    _ = ∫ x, fderiv ℝ f x 1 * gaussianPDFReal 0 1 x := by
      rw [hparts']
      simp
    _ = ∫ x, gaussianPDFReal 0 1 x * fderiv ℝ f x 1 := by
      congr 1
      funext x
      ring

end RegularityStructures

end
