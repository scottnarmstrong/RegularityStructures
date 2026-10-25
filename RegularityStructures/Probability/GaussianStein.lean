/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.GaussianPoincare
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The explicit one-dimensional Gaussian Stein primitive

The primitive used here is the standard solution of the Gaussian Stein equation.  The
construction is separated from the final estimate so that its differentiability and its tail
conditions can be discharged as ordinary analytic lemmas.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Real

namespace RegularityStructures

def gaussianSteinPrimitive (q : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in Set.Iic x, q t

def gaussianSteinSolution (f : ℝ → ℝ) (m x : ℝ) : ℝ :=
  √(2 * π) * rexp (x ^ 2 / 2) *
    gaussianSteinPrimitive (fun t => (f t - m) * gaussianPDFReal 0 1 t) x

private lemma integral_Iic_eq_Iic_zero_add_intervalIntegral {q : ℝ → ℝ}
    (hq : Integrable q (volume : Measure ℝ)) (x : ℝ) :
    (∫ t in Set.Iic x, q t) =
      (∫ t in Set.Iic (0 : ℝ), q t) + ∫ t in (0 : ℝ)..x, q t := by
  rcases le_total (0 : ℝ) x with hx | hx
  · have h := intervalIntegral.integral_Iic_sub_Iic (f := q) (μ := volume)
      (a := (0 : ℝ)) (b := x) hq.integrableOn hq.integrableOn
    rw [sub_eq_iff_eq_add'] at h
    simpa [gaussianSteinPrimitive] using h
  · have h := intervalIntegral.integral_Iic_sub_Iic (f := q) (μ := volume)
      (a := (0 : ℝ)) (b := x) hq.integrableOn hq.integrableOn
    rw [sub_eq_iff_eq_add'] at h
    simpa [gaussianSteinPrimitive, add_comm] using h

theorem hasDerivAt_gaussianSteinPrimitive {q : ℝ → ℝ} (hqcont : Continuous q)
    (hq : Integrable q (volume : Measure ℝ)) (x : ℝ) :
    HasDerivAt (gaussianSteinPrimitive q) (q x) x := by
  rw [show gaussianSteinPrimitive q =
      (fun y => (∫ t in Set.Iic (0 : ℝ), q t) + ∫ t in (0 : ℝ)..y, q t) by
    funext y
    exact integral_Iic_eq_Iic_zero_add_intervalIntegral hq y]
  exact (hqcont.integral_hasStrictDerivAt (0 : ℝ) x).hasDerivAt.const_add _

theorem hasDerivAt_gaussianSteinSolution {f : ℝ → ℝ} {m : ℝ}
    (hf : ContDiff ℝ 1 f)
    (hq : Integrable (fun t => (f t - m) * gaussianPDFReal 0 1 t)
      (volume : Measure ℝ)) (x : ℝ) :
    HasDerivAt (gaussianSteinSolution f m) (x * gaussianSteinSolution f m x + (f x - m)) x := by
  have hpdf : Continuous (gaussianPDFReal 0 1) := by
    rw [gaussianPDFReal_def]
    fun_prop
  have hqcont : Continuous (fun t => (f t - m) * gaussianPDFReal 0 1 t) :=
    (hf.continuous.sub continuous_const).mul hpdf
  have hprimitive := hasDerivAt_gaussianSteinPrimitive hqcont hq x
  have hexp : HasDerivAt (fun y : ℝ => rexp (y ^ 2 / 2))
      (x * rexp (x ^ 2 / 2)) x := by
    have harg : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
      simpa [Function.comp_def] using ((hasDerivAt_id x).pow 2).div_const (2 : ℝ)
    simpa [Function.comp_def, mul_comm] using (Real.hasDerivAt_exp _).comp x harg
  have hmul := (hasDerivAt_const x (√(2 * π))).mul (hexp.mul hprimitive)
  simp only [zero_mul, zero_add] at hmul
  have hpoint : √(2 * π) * rexp (x ^ 2 / 2) *
      ((f x - m) * gaussianPDFReal 0 1 x) = f x - m := by
    simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero]
    have hπ : 0 < (2 * π : ℝ) := by positivity
    have hsqrt : √(2 * π) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hπ)
    field_simp [hsqrt]
    calc
      rexp (x ^ 2 / 2) * (f x - m) * rexp (-(x ^ 2 / 2)) =
          (f x - m) * (rexp (x ^ 2 / 2) * rexp (-(x ^ 2 / 2))) := by ring
      _ = f x - m := by simp [← Real.exp_add]
  have hmul' := hmul
  change HasDerivAt
    (fun y => √(2 * π) *
      (rexp (y ^ 2 / 2) * gaussianSteinPrimitive
        (fun t => (f t - m) * gaussianPDFReal 0 1 t) y))
    (√(2 * π) *
      (x * rexp (x ^ 2 / 2) * gaussianSteinPrimitive
          (fun t => (f t - m) * gaussianPDFReal 0 1 t) x +
        rexp (x ^ 2 / 2) * ((f x - m) * gaussianPDFReal 0 1 x))) x at hmul'
  have hfun :
      (fun y => √(2 * π) *
        (rexp (y ^ 2 / 2) * gaussianSteinPrimitive
          (fun t => (f t - m) * gaussianPDFReal 0 1 t) y)) =
        gaussianSteinSolution f m := by
    funext y
    simp only [gaussianSteinSolution]
    ring
  rw [hfun] at hmul'
  apply hmul'.congr_deriv
  calc
    √(2 * π) *
          (x * rexp (x ^ 2 / 2) * gaussianSteinPrimitive
              (fun t => (f t - m) * gaussianPDFReal 0 1 t) x +
            rexp (x ^ 2 / 2) * ((f x - m) * gaussianPDFReal 0 1 x)) =
        x * gaussianSteinSolution f m x +
          √(2 * π) * rexp (x ^ 2 / 2) *
            ((f x - m) * gaussianPDFReal 0 1 x) := by
      simp only [gaussianSteinSolution]
      ring
    _ = x * gaussianSteinSolution f m x + (f x - m) := by rw [hpoint]

theorem contDiff_gaussianSteinSolution {f : ℝ → ℝ} {m : ℝ}
    (hf : ContDiff ℝ 1 f)
    (hq : Integrable (fun t => (f t - m) * gaussianPDFReal 0 1 t)
      (volume : Measure ℝ)) :
    ContDiff ℝ 1 (gaussianSteinSolution f m) := by
  let q : ℝ → ℝ := fun t => (f t - m) * gaussianPDFReal 0 1 t
  have hqcont : Continuous q := by
    dsimp [q]
    have hpdf : Continuous (gaussianPDFReal 0 1) := by
      rw [gaussianPDFReal_def]
      fun_prop
    exact (hf.continuous.sub continuous_const).mul hpdf
  have hprim_deriv : ∀ x, HasDerivAt (gaussianSteinPrimitive q) (q x) x := by
    intro x
    exact hasDerivAt_gaussianSteinPrimitive hqcont (by simpa [q] using hq) x
  have hprim_diff : Differentiable ℝ (gaussianSteinPrimitive q) := by
    intro x
    exact (hprim_deriv x).differentiableAt
  have hprim_deriv_eq : deriv (gaussianSteinPrimitive q) = q := by
    funext x
    exact (hprim_deriv x).deriv
  have hprim_cd : ContDiff ℝ 1 (gaussianSteinPrimitive q) := by
    rw [contDiff_one_iff_deriv]
    refine ⟨hprim_diff, ?_⟩
    rw [hprim_deriv_eq]
    exact hqcont
  have hquad : ContDiff ℝ 1 (fun x : ℝ => x ^ 2 / 2) := by
    fun_prop
  have hexp : ContDiff ℝ 1 (fun x : ℝ => rexp (x ^ 2 / 2)) := hquad.exp
  have hsolution : ContDiff ℝ 1
      (fun x => √(2 * π) *
        (rexp (x ^ 2 / 2) * gaussianSteinPrimitive q x)) := by
    exact contDiff_const.mul (hexp.mul hprim_cd)
  have hEq : (fun x => √(2 * π) * rexp (x ^ 2 / 2) *
      gaussianSteinPrimitive q x) =
      (fun x => √(2 * π) *
        (rexp (x ^ 2 / 2) * gaussianSteinPrimitive q x)) := by
    funext x
    ring
  change ContDiff ℝ 1
    (fun x => √(2 * π) * rexp (x ^ 2 / 2) *
      gaussianSteinPrimitive q x)
  rw [hEq]
  exact hsolution

theorem gaussian_poincare_one_dimensional_of_explicit_stein {f : ℝ → ℝ}
    (hcont_f : ContDiff ℝ 1 f)
    (hgrowth_f : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ x : ℝ, |f x| + ‖fderiv ℝ f x‖ ≤ C * (1 + ‖x‖) ^ N)
    (hq : Integrable
      (fun x => (f x - ∫ y, f y ∂(gaussianReal 0 1)) * gaussianPDFReal 0 1 x)
      (volume : Measure ℝ))
    (hgrowth_prod : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ x : ℝ,
        |(f x - ∫ y, f y ∂(gaussianReal 0 1)) * gaussianSteinSolution f
            (∫ y, f y ∂(gaussianReal 0 1)) x| +
          ‖fderiv ℝ ((fun y => f y - ∫ z, f z ∂(gaussianReal 0 1)) *
            gaussianSteinSolution f (∫ y, f y ∂(gaussianReal 0 1))) x‖ ≤
            C * (1 + ‖x‖) ^ N)
    (hgrowth_u_sq : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ x : ℝ, |gaussianSteinSolution f (∫ y, f y ∂(gaussianReal 0 1)) x ^ 2| +
        ‖fderiv ℝ (fun y => gaussianSteinSolution f
          (∫ z, f z ∂(gaussianReal 0 1)) y ^ 2) x‖ ≤ C * (1 + ‖x‖) ^ N)
    (hgrowth_x_u_sq : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ x : ℝ, |x * gaussianSteinSolution f
          (∫ y, f y ∂(gaussianReal 0 1)) x ^ 2| +
        ‖fderiv ℝ (fun y => y * gaussianSteinSolution f
          (∫ z, f z ∂(gaussianReal 0 1)) y ^ 2) x‖ ≤ C * (1 + ‖x‖) ^ N)
    (hcenter_sq : Integrable
      (fun x => (f x - ∫ y, f y ∂(gaussianReal 0 1)) ^ 2)
      (gaussianReal 0 1))
    (hderiv_sq : Integrable (fun x => (fderiv ℝ f x 1) ^ 2)
      (gaussianReal 0 1))
    (hu_sq : Integrable
      (fun x => gaussianSteinSolution f (∫ y, f y ∂(gaussianReal 0 1)) x ^ 2)
      (gaussianReal 0 1))
    (hderiv_memLp : MemLp (fun x => fderiv ℝ f x 1) 2 (gaussianReal 0 1))
    (hu_memLp : MemLp (gaussianSteinSolution f
      (∫ y, f y ∂(gaussianReal 0 1))) 2 (gaussianReal 0 1))
    (hprod : Integrable
      (fun x => (f x - ∫ y, f y ∂(gaussianReal 0 1)) *
        gaussianSteinSolution f (∫ z, f z ∂(gaussianReal 0 1)) x *
        gaussianPDFReal 0 1 x) (volume : Measure ℝ))
    (hprod_deriv : Integrable
      (fun x =>
        (fderiv ℝ f x 1 * gaussianSteinSolution f
            (∫ z, f z ∂(gaussianReal 0 1)) x +
          (f x - ∫ z, f z ∂(gaussianReal 0 1)) *
            fderiv ℝ (gaussianSteinSolution f
              (∫ z, f z ∂(gaussianReal 0 1))) x 1) *
          gaussianPDFReal 0 1 x) (volume : Measure ℝ))
    (hprod_x : Integrable
      (fun x => x * (f x - ∫ y, f y ∂(gaussianReal 0 1)) *
        gaussianSteinSolution f (∫ z, f z ∂(gaussianReal 0 1)) x *
        gaussianPDFReal 0 1 x) (volume : Measure ℝ))
    (h_g_uprime : Integrable
      (fun x => (f x - ∫ y, f y ∂(gaussianReal 0 1)) *
        fderiv ℝ (gaussianSteinSolution f
          (∫ z, f z ∂(gaussianReal 0 1))) x 1) (gaussianReal 0 1))
    (h_x_g_u : Integrable
      (fun x => x * (f x - ∫ y, f y ∂(gaussianReal 0 1)) *
        gaussianSteinSolution f (∫ z, f z ∂(gaussianReal 0 1)) x)
      (gaussianReal 0 1))
    (h_fprime_u : Integrable
      (fun x => fderiv ℝ f x 1 * gaussianSteinSolution f
        (∫ y, f y ∂(gaussianReal 0 1)) x) (gaussianReal 0 1))
    (h_uprime_sq_gaussian : Integrable
      (fun x => (fderiv ℝ (gaussianSteinSolution f
        (∫ y, f y ∂(gaussianReal 0 1))) x 1) ^ 2)
      (gaussianReal 0 1))
    (h_x_sq_u_sq_gaussian : Integrable
      (fun x => x ^ 2 * gaussianSteinSolution f
        (∫ y, f y ∂(gaussianReal 0 1)) x ^ 2) (gaussianReal 0 1))
    (h_x_u_uprime_gaussian : Integrable
      (fun x => x * gaussianSteinSolution f
        (∫ y, f y ∂(gaussianReal 0 1)) x *
        fderiv ℝ (gaussianSteinSolution f
          (∫ y, f y ∂(gaussianReal 0 1))) x 1) (gaussianReal 0 1))
    (hu_deriv_sq : Integrable
      (fun x => (fderiv ℝ (gaussianSteinSolution f
        (∫ y, f y ∂(gaussianReal 0 1))) x 1) ^ 2 * gaussianPDFReal 0 1 x)
      (volume : Measure ℝ))
    (hu_x_sq : Integrable
      (fun x => x ^ 2 * gaussianSteinSolution f
        (∫ y, f y ∂(gaussianReal 0 1)) x ^ 2 * gaussianPDFReal 0 1 x)
      (volume : Measure ℝ))
    (hu_x_deriv : Integrable
      (fun x => x * gaussianSteinSolution f
        (∫ y, f y ∂(gaussianReal 0 1)) x *
        fderiv ℝ (gaussianSteinSolution f
          (∫ y, f y ∂(gaussianReal 0 1))) x 1 * gaussianPDFReal 0 1 x)
      (volume : Measure ℝ))
    (hu_sq_volume : Integrable
      (fun x => gaussianSteinSolution f
        (∫ y, f y ∂(gaussianReal 0 1)) x ^ 2 * gaussianPDFReal 0 1 x)
      (volume : Measure ℝ))
    (hu_sq_deriv_volume : Integrable
      (fun x => 2 * gaussianSteinSolution f
        (∫ y, f y ∂(gaussianReal 0 1)) x *
        fderiv ℝ (gaussianSteinSolution f
          (∫ y, f y ∂(gaussianReal 0 1))) x 1 * gaussianPDFReal 0 1 x)
      (volume : Measure ℝ))
    (hu_x_sq_volume : Integrable
      (fun x => x * gaussianSteinSolution f
        (∫ y, f y ∂(gaussianReal 0 1)) x ^ 2 * gaussianPDFReal 0 1 x)
      (volume : Measure ℝ))
    (hu_x_sq_deriv_volume : Integrable
      (fun x =>
        (gaussianSteinSolution f (∫ y, f y ∂(gaussianReal 0 1)) x ^ 2 +
          2 * x * gaussianSteinSolution f
            (∫ y, f y ∂(gaussianReal 0 1)) x *
            fderiv ℝ (gaussianSteinSolution f
              (∫ y, f y ∂(gaussianReal 0 1))) x 1) *
          gaussianPDFReal 0 1 x) (volume : Measure ℝ)) :
    Var[(fun x => f x); gaussianReal 0 1] ≤
      ∫ x, (fderiv ℝ f x 1) ^ 2 ∂(gaussianReal 0 1) := by
  let m : ℝ := ∫ y, f y ∂(gaussianReal 0 1)
  have hu_cont : ContDiff ℝ 1 (gaussianSteinSolution f m) := by
    exact contDiff_gaussianSteinSolution hcont_f (by simpa [m] using hq)
  have hstein : ∀ x, f x - ∫ y, f y ∂(gaussianReal 0 1) =
      fderiv ℝ (gaussianSteinSolution f m) x 1 -
        x * gaussianSteinSolution f m x := by
    intro x
    have h := hasDerivAt_gaussianSteinSolution hcont_f (by simpa [m] using hq) x
    rw [fderiv_apply_one_eq_deriv]
    have hd := h.deriv
    dsimp [m] at hd ⊢
    linarith
  apply gaussian_poincare_one_dimensional_of_stein hcont_f hu_cont hgrowth_f
    (by simpa [m] using hgrowth_prod) (by simpa [m] using hgrowth_u_sq)
    (by simpa [m] using hgrowth_x_u_sq) hstein
    hcenter_sq hderiv_sq hu_sq hderiv_memLp hu_memLp
    (by simpa [m] using hprod) (by simpa [m] using hprod_deriv)
    (by simpa [m] using hprod_x) (by simpa [m] using h_g_uprime)
    (by simpa [m] using h_x_g_u) (by simpa [m] using h_fprime_u)
    (by simpa [m] using h_uprime_sq_gaussian)
    (by simpa [m] using h_x_sq_u_sq_gaussian)
    (by simpa [m] using h_x_u_uprime_gaussian)
    (by simpa [m] using hu_deriv_sq) (by simpa [m] using hu_x_sq)
    (by simpa [m] using hu_x_deriv) (by simpa [m] using hu_sq_volume)
    (by simpa [m] using hu_sq_deriv_volume) (by simpa [m] using hu_x_sq_volume)
    (by simpa [m] using hu_x_sq_deriv_volume)

end RegularityStructures

end
