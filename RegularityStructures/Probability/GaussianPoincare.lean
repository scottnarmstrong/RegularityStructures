/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.Poincare
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# The one-dimensional Gaussian Poincare estimate

This module contains the Stein-solution proof of the one-dimensional Gaussian Poincare
inequality. The analytic hypotheses are written as ordinary regularity and integrability
arguments of the theorem; the inequality itself is not packaged as a proposition-valued target.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Real

namespace RegularityStructures

private lemma fderiv_mul_one_dimensional {f g : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) (x : ℝ) :
    fderiv ℝ (fun y => f y * g y) x 1 =
      fderiv ℝ f x 1 * g x + f x * fderiv ℝ g x 1 := by
  rw [fderiv_apply_one_eq_deriv]
  change deriv (f * g) x = deriv f x * g x + f x * deriv g x
  exact ((hf.differentiable one_ne_zero x).hasDerivAt.mul
    (hg.differentiable one_ne_zero x).hasDerivAt).deriv

private lemma fderiv_sq_one_dimensional {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u) (x : ℝ) :
    fderiv ℝ (fun y => u y ^ 2) x 1 = 2 * u x * fderiv ℝ u x 1 := by
  rw [fderiv_apply_one_eq_deriv]
  change deriv (u ^ 2) x = 2 * u x * deriv u x
  have h := ((hu.differentiable one_ne_zero x).hasDerivAt.pow 2)
  convert h.deriv using 1
  norm_num

private lemma fderiv_mul_sq_one_dimensional {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u) (x : ℝ) :
    fderiv ℝ (fun y => y * u y ^ 2) x 1 =
      u x ^ 2 + 2 * x * u x * fderiv ℝ u x 1 := by
  rw [fderiv_apply_one_eq_deriv]
  change deriv (id * (u ^ 2)) x = _
  have hu2 : HasDerivAt (fun y => u y ^ 2) (2 * u x * deriv u x) x := by
    have h := ((hu.differentiable one_ne_zero x).hasDerivAt.pow 2)
    change HasDerivAt (u ^ 2) (2 * u x * deriv u x) x
    convert h using 1
    norm_num
  have hmul := (hasDerivAt_id x).mul hu2
  convert hmul.deriv using 1
  rw [fderiv_apply_one_eq_deriv]
  norm_num
  ring

private lemma gaussian_integral_by_parts_for_product {h : ℝ → ℝ}
    (hh : ContDiff ℝ 1 h)
    (hgrowth : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ x : ℝ, |h x| + ‖fderiv ℝ h x‖ ≤ C * (1 + ‖x‖) ^ N)
    (hprod : Integrable (fun x => h x * gaussianPDFReal 0 1 x) volume)
    (hderiv : Integrable (fun x => fderiv ℝ h x 1 * gaussianPDFReal 0 1 x) volume)
    (hx : Integrable (fun x => x * h x * gaussianPDFReal 0 1 x) volume) :
    ∫ x, x * h x ∂(gaussianReal 0 1) =
      ∫ x, fderiv ℝ h x 1 ∂(gaussianReal 0 1) := by
  exact gaussian_integration_by_parts_one_dimensional hh hgrowth hprod hderiv hx

theorem gaussian_poincare_one_dimensional_of_stein {f u : ℝ → ℝ}
    (hcont_f : ContDiff ℝ 1 f)
    (hcont_u : ContDiff ℝ 1 u)
    (_hgrowth : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ x : ℝ, |f x| + ‖fderiv ℝ f x‖ ≤ C * (1 + ‖x‖) ^ N)
    (hgrowth_prod : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ x : ℝ,
        |(f x - ∫ y, f y ∂(gaussianReal 0 1)) * u x| +
          ‖fderiv ℝ ((fun y => f y - ∫ z, f z ∂(gaussianReal 0 1)) * u) x‖ ≤
            C * (1 + ‖x‖) ^ N)
    (hgrowth_u_sq : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ x : ℝ, |u x ^ 2| + ‖fderiv ℝ (fun y => u y ^ 2) x‖ ≤ C * (1 + ‖x‖) ^ N)
    (hgrowth_x_u_sq : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ x : ℝ, |x * u x ^ 2| + ‖fderiv ℝ (fun y => y * u y ^ 2) x‖ ≤
        C * (1 + ‖x‖) ^ N)
    (hstein : ∀ x, f x - ∫ y, f y ∂(gaussianReal 0 1) =
      fderiv ℝ u x 1 - x * u x)
    (_hcenter_sq : Integrable
      (fun x => (f x - ∫ y, f y ∂(gaussianReal 0 1)) ^ 2)
      (gaussianReal 0 1))
    (_hderiv_sq : Integrable (fun x => (fderiv ℝ f x 1) ^ 2)
      (gaussianReal 0 1))
    (hu_sq : Integrable (fun x => u x ^ 2) (gaussianReal 0 1))
    (hderiv_memLp : MemLp (fun x => fderiv ℝ f x 1) 2 (gaussianReal 0 1))
    (hu_memLp : MemLp u 2 (gaussianReal 0 1))
    (hprod : Integrable
      (fun x => (f x - ∫ y, f y ∂(gaussianReal 0 1)) * u x * gaussianPDFReal 0 1 x)
      volume)
    (hprod_deriv : Integrable
      (fun x =>
        (fderiv ℝ f x 1 * u x +
          (f x - ∫ y, f y ∂(gaussianReal 0 1)) * fderiv ℝ u x 1) *
          gaussianPDFReal 0 1 x)
      volume)
    (hprod_x : Integrable
      (fun x => x * (f x - ∫ y, f y ∂(gaussianReal 0 1)) * u x *
        gaussianPDFReal 0 1 x)
      volume)
    (h_g_uprime : Integrable
      (fun x => (f x - ∫ y, f y ∂(gaussianReal 0 1)) * fderiv ℝ u x 1)
      (gaussianReal 0 1))
    (h_x_g_u : Integrable
      (fun x => x * (f x - ∫ y, f y ∂(gaussianReal 0 1)) * u x)
      (gaussianReal 0 1))
    (h_fprime_u : Integrable
      (fun x => fderiv ℝ f x 1 * u x) (gaussianReal 0 1))
    (h_uprime_sq_gaussian : Integrable
      (fun x => (fderiv ℝ u x 1) ^ 2) (gaussianReal 0 1))
    (h_x_sq_u_sq_gaussian : Integrable
      (fun x => x ^ 2 * u x ^ 2) (gaussianReal 0 1))
    (h_x_u_uprime_gaussian : Integrable
      (fun x => x * u x * fderiv ℝ u x 1) (gaussianReal 0 1))
    (_hu_deriv_sq : Integrable
      (fun x => (fderiv ℝ u x 1) ^ 2 * gaussianPDFReal 0 1 x) volume)
    (hu_x_sq : Integrable
      (fun x => x ^ 2 * u x ^ 2 * gaussianPDFReal 0 1 x) volume)
    (_hu_x_deriv : Integrable
      (fun x => x * u x * fderiv ℝ u x 1 * gaussianPDFReal 0 1 x) volume)
    (hu_sq_volume : Integrable
      (fun x => u x ^ 2 * gaussianPDFReal 0 1 x) volume)
    (hu_sq_deriv_volume : Integrable
      (fun x => 2 * u x * fderiv ℝ u x 1 * gaussianPDFReal 0 1 x) volume)
    (hu_x_sq_volume : Integrable
      (fun x => x * u x ^ 2 * gaussianPDFReal 0 1 x) volume)
    (hu_x_sq_deriv_volume : Integrable
      (fun x => (u x ^ 2 + 2 * x * u x * fderiv ℝ u x 1) *
        gaussianPDFReal 0 1 x) volume) :
    Var[(fun x => f x); gaussianReal 0 1] ≤
      ∫ x, (fderiv ℝ f x 1) ^ 2 ∂(gaussianReal 0 1) := by
  let m : ℝ := ∫ y, f y ∂(gaussianReal 0 1)
  let g : ℝ → ℝ := fun x => f x - m
  have hprod_ibp :
      ∫ x, x * g x * u x ∂(gaussianReal 0 1) =
        ∫ x, (fderiv ℝ f x 1 * u x + g x * fderiv ℝ u x 1) ∂(gaussianReal 0 1) := by
    have hhcont : ContDiff ℝ 1 (fun x => (f x - m) * u x) :=
      (hcont_f.sub (contDiff_const (n := (1 : WithTop ℕ∞)))).mul hcont_u
    have hderiv : Integrable
        (fun x => fderiv ℝ (fun y => (f y - m) * u y) x 1 *
          gaussianPDFReal 0 1 x) volume := by
      have hpoint : ∀ x, fderiv ℝ (fun y => (f y - m) * u y) x 1 =
          fderiv ℝ f x 1 * u x +
            (f x - ∫ y, f y ∂(gaussianReal 0 1)) * fderiv ℝ u x 1 := by
        intro x
        have hsub : ContDiff ℝ 1 (fun y => f y - m) :=
          hcont_f.sub (contDiff_const (n := (1 : WithTop ℕ∞)))
        have h := fderiv_mul_one_dimensional hsub hcont_u x
        rw [fderiv_sub_const] at h
        simpa [m] using h
      refine hprod_deriv.congr ?_
      filter_upwards [] with x
      rw [hpoint]
    have hprod_x' : Integrable
        (fun x => x * ((f x - m) * u x) * gaussianPDFReal 0 1 x) volume := by
      refine hprod_x.congr ?_
      filter_upwards [] with x
      dsimp [m]
      ring
    have h := gaussian_integral_by_parts_for_product
      (h := fun x => (f x - m) * u x) hhcont
      hgrowth_prod hprod hderiv hprod_x'
    have hpoint : ∀ x, fderiv ℝ (fun y => (f y - m) * u y) x 1 =
        fderiv ℝ f x 1 * u x + g x * fderiv ℝ u x 1 := by
      intro x
      have hsub : ContDiff ℝ 1 (fun y => f y - m) :=
        hcont_f.sub (contDiff_const (n := (1 : WithTop ℕ∞)))
      have h := fderiv_mul_one_dimensional hsub hcont_u x
      rw [fderiv_sub_const] at h
      simpa [m, g] using h
    rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)] at h
    simpa only [g, m, mul_assoc] using h
  have h_u_sq_ibp :
      ∫ x, x * u x ^ 2 ∂(gaussianReal 0 1) =
        ∫ x, 2 * u x * fderiv ℝ u x 1 ∂(gaussianReal 0 1) := by
    have hderiv : Integrable
        (fun x => fderiv ℝ (fun y => u y ^ 2) x 1 * gaussianPDFReal 0 1 x) volume := by
      refine hu_sq_deriv_volume.congr ?_
      filter_upwards [] with x
      rw [fderiv_sq_one_dimensional hcont_u]
    have hhcont : ContDiff ℝ 1 (fun x => u x ^ 2) := hcont_u.pow 2
    have h := gaussian_integral_by_parts_for_product
      hhcont hgrowth_u_sq hu_sq_volume hderiv hu_x_sq_volume
    rw [integral_congr_ae (Filter.Eventually.of_forall (fderiv_sq_one_dimensional hcont_u))] at h
    exact h
  have h_x_u_sq_ibp :
      ∫ x, x ^ 2 * u x ^ 2 ∂(gaussianReal 0 1) =
        ∫ x, (u x ^ 2 + 2 * x * u x * fderiv ℝ u x 1) ∂(gaussianReal 0 1) := by
    have hderiv : Integrable
        (fun x => fderiv ℝ (fun y => y * u y ^ 2) x 1 * gaussianPDFReal 0 1 x) volume := by
      refine hu_x_sq_deriv_volume.congr ?_
      filter_upwards [] with x
      rw [fderiv_mul_sq_one_dimensional hcont_u]
    have hhcont : ContDiff ℝ 1 (fun x => x * u x ^ 2) :=
      contDiff_id.mul (hcont_u.pow 2)
    have h := gaussian_integral_by_parts_for_product
      (h := fun x => x * u x ^ 2) hhcont hgrowth_x_u_sq
        hu_x_sq_volume hderiv (by
          simpa only [pow_two, mul_assoc] using hu_x_sq)
    rw [integral_congr_ae (Filter.Eventually.of_forall (fderiv_mul_sq_one_dimensional hcont_u))] at h
    convert h using 1
    congr 1
    funext x
    ring
  have h_center_eq :
      Var[(fun x => f x); gaussianReal 0 1] =
        ∫ x, g x ^ 2 ∂(gaussianReal 0 1) := by
    simpa only [g, m] using
      (variance_eq_integral hcont_f.continuous.aemeasurable)
  have h_stein_integral :
      ∫ x, g x ^ 2 ∂(gaussianReal 0 1) =
        -∫ x, (fderiv ℝ f x 1) * u x ∂(gaussianReal 0 1) := by
    have hsplit :
        ∫ x, g x * (fderiv ℝ u x 1 - x * u x) ∂(gaussianReal 0 1) =
          (∫ x, g x * fderiv ℝ u x 1 ∂(gaussianReal 0 1)) -
            ∫ x, x * g x * u x ∂(gaussianReal 0 1) := by
      rw [← integral_sub h_g_uprime h_x_g_u]
      congr 1
      funext x
      ring
    have hpoint : ∀ x, g x ^ 2 = g x * (fderiv ℝ u x 1 - x * u x) := by
      intro x
      have hg : g x = fderiv ℝ u x 1 - x * u x := by
        simpa [g, m] using hstein x
      rw [hg]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
    rw [hsplit, hprod_ibp]
    rw [integral_add h_fprime_u h_g_uprime]
    ring
  have h_adjoint :
      ∫ x, (fderiv ℝ u x 1 - x * u x) ^ 2 ∂(gaussianReal 0 1) =
        (∫ x, (fderiv ℝ u x 1) ^ 2 ∂(gaussianReal 0 1)) +
          ∫ x, u x ^ 2 ∂(gaussianReal 0 1) := by
    have h_expand : ∀ x : ℝ,
        (fderiv ℝ u x 1 - x * u x) ^ 2 =
          (fderiv ℝ u x 1) ^ 2 - 2 * (x * u x * fderiv ℝ u x 1) +
            x ^ 2 * u x ^ 2 := by
      intro x
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall h_expand)]
    have hsub_int := h_uprime_sq_gaussian.sub (h_x_u_uprime_gaussian.const_mul 2)
    have hsum :
        (fun x => (fderiv ℝ u x 1) ^ 2 - 2 * (x * u x * fderiv ℝ u x 1) +
            x ^ 2 * u x ^ 2) =
          (fun x => (fderiv ℝ u x 1) ^ 2 - 2 * (x * u x * fderiv ℝ u x 1)) +
            (fun x => x ^ 2 * u x ^ 2) := by
      funext x
      rfl
    rw [hsum]
    have hi := integral_add hsub_int h_x_sq_u_sq_gaussian
    calc
      _ = (∫ x, (fderiv ℝ u x 1) ^ 2 - 2 * (x * u x * fderiv ℝ u x 1) ∂
          (gaussianReal 0 1)) +
          ∫ x, x ^ 2 * u x ^ 2 ∂(gaussianReal 0 1) := by
        convert hi using 1
      _ = _ := by
        have hx' :
            ∫ x, x ^ 2 * u x ^ 2 ∂(gaussianReal 0 1) =
              ∫ x, u x ^ 2 + 2 * x * u x * fderiv ℝ u x 1 ∂(gaussianReal 0 1) := by
          convert h_x_u_sq_ibp using 1
        have hsub' :
            ∫ x, (fderiv ℝ u x 1) ^ 2 - 2 * (x * u x * fderiv ℝ u x 1) ∂
                (gaussianReal 0 1) =
              (∫ x, (fderiv ℝ u x 1) ^ 2 ∂(gaussianReal 0 1)) -
                ∫ x, 2 * (x * u x * fderiv ℝ u x 1) ∂(gaussianReal 0 1) := by
          convert integral_sub h_uprime_sq_gaussian
            (h_x_u_uprime_gaussian.const_mul 2) using 1
        have hadd' :
            ∫ x, u x ^ 2 + 2 * x * u x * fderiv ℝ u x 1 ∂(gaussianReal 0 1) =
              (∫ x, u x ^ 2 ∂(gaussianReal 0 1)) +
                ∫ x, 2 * (x * u x * fderiv ℝ u x 1) ∂(gaussianReal 0 1) := by
          convert integral_add hu_sq (h_x_u_uprime_gaussian.const_mul 2) using 1
          congr 1
          funext x
          ring
        rw [hx', hsub', hadd']
        ring
  have h_center_eq_stein :
      Var[(fun x => f x); gaussianReal 0 1] =
        (∫ x, (fderiv ℝ u x 1) ^ 2 ∂(gaussianReal 0 1)) +
          ∫ x, u x ^ 2 ∂(gaussianReal 0 1) := by
    rw [h_center_eq]
    rw [show (fun x => g x ^ 2) =
        (fun x => (fderiv ℝ u x 1 - x * u x) ^ 2) by
      funext x
      have hg : g x = fderiv ℝ u x 1 - x * u x := by
        simpa [g, m] using hstein x
      rw [hg]]
    exact h_adjoint
  have h_cauchy :
      -∫ x, (fderiv ℝ f x 1) * u x ∂(gaussianReal 0 1) ≤
        (∫ x, (fderiv ℝ f x 1) ^ 2 ∂(gaussianReal 0 1)) ^ (1 / 2 : ℝ) *
          (∫ x, u x ^ 2 ∂(gaussianReal 0 1)) ^ (1 / 2 : ℝ) := by
    have hderiv_abs : MemLp (fun x => |fderiv ℝ f x 1|)
        (ENNReal.ofReal (2 : ℝ)) (gaussianReal 0 1) := by
      convert hderiv_memLp.abs using 1
      · funext x
        rfl
      · norm_num
    have hu_abs : MemLp (fun x => |u x|)
        (ENNReal.ofReal (2 : ℝ)) (gaussianReal 0 1) := by
      convert hu_memLp.abs using 1
      · funext x
        rfl
      · norm_num
    have h' := integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := gaussianReal 0 1) (p := (2 : ℝ)) (q := (2 : ℝ))
      Real.HolderConjugate.two_two
      (ae_of_all _ fun x => abs_nonneg ((fderiv ℝ f x 1)))
      (ae_of_all _ fun x => abs_nonneg (u x)) hderiv_abs hu_abs
    have h'₂ :
        (∫ x, |fderiv ℝ f x 1| * |u x| ∂(gaussianReal 0 1)) ≤
          (∫ x, (fderiv ℝ f x 1) ^ 2 ∂(gaussianReal 0 1)) ^ (1 / 2 : ℝ) *
            (∫ x, u x ^ 2 ∂(gaussianReal 0 1)) ^ (1 / 2 : ℝ) := by
      calc
        _ ≤ (∫ x, |fderiv ℝ f x 1| ^ 2 ∂(gaussianReal 0 1)) ^ (1 / 2 : ℝ) *
            (∫ x, |u x| ^ 2 ∂(gaussianReal 0 1)) ^ (1 / 2 : ℝ) := h'
        _ = _ := by
          congr 1
          · congr 1
            apply integral_congr_ae
            filter_upwards [] with x
            norm_num [Real.rpow_two]
          · congr 1
            apply integral_congr_ae
            filter_upwards [] with x
            norm_num [Real.rpow_two]
    have habs :
        -∫ x, (fderiv ℝ f x 1) * u x ∂(gaussianReal 0 1) ≤
          ∫ x, |fderiv ℝ f x 1| * |u x| ∂(gaussianReal 0 1) := by
      calc
        _ ≤ |∫ x, (fderiv ℝ f x 1) * u x ∂(gaussianReal 0 1)| :=
          neg_le_abs _
        _ ≤ ∫ x, |(fderiv ℝ f x 1) * u x| ∂(gaussianReal 0 1) :=
          abs_integral_le_integral_abs
        _ = ∫ x, |fderiv ℝ f x 1| * |u x| ∂(gaussianReal 0 1) := by
          congr 1
          funext x
          rw [abs_mul]
    calc
      _ ≤ ∫ x, |fderiv ℝ f x 1| * |u x| ∂(gaussianReal 0 1) := habs
      _ ≤ _ := h'₂
  have h_variance_nonneg :
      0 ≤ Var[(fun x => f x); gaussianReal 0 1] := variance_nonneg _ _
  have h_energy_nonneg :
      0 ≤ ∫ x, (fderiv ℝ f x 1) ^ 2 ∂(gaussianReal 0 1) := by
    exact integral_nonneg fun x => sq_nonneg _
  by_cases hzero : Var[(fun x => f x); gaussianReal 0 1] = 0
  · simpa [hzero] using h_energy_nonneg
  have hvar_pos : 0 < Var[(fun x => f x); gaussianReal 0 1] :=
    lt_of_le_of_ne h_variance_nonneg (Ne.symm hzero)
  have hu_le_var :
      ∫ x, u x ^ 2 ∂(gaussianReal 0 1) ≤ Var[(fun x => f x); gaussianReal 0 1] := by
    have hup_nonneg : 0 ≤ ∫ x, (fderiv ℝ u x 1) ^ 2 ∂(gaussianReal 0 1) :=
      integral_nonneg (μ := gaussianReal 0 1) (fun x => sq_nonneg _)
    nlinarith [h_center_eq_stein]
  have hsq :
      (Var[(fun x => f x); gaussianReal 0 1]) ^ 2 ≤
        (∫ x, (fderiv ℝ f x 1) ^ 2 ∂(gaussianReal 0 1)) *
          ∫ x, u x ^ 2 ∂(gaussianReal 0 1) := by
    have hA : Var[(fun x => f x); gaussianReal 0 1] =
        -∫ x, (fderiv ℝ f x 1) * u x ∂(gaussianReal 0 1) :=
      h_center_eq.trans h_stein_integral
    rw [hA]
    have hnonneg : 0 ≤ -∫ x, (fderiv ℝ f x 1) * u x ∂(gaussianReal 0 1) := by
      rw [← h_stein_integral, ← h_center_eq]
      exact h_variance_nonneg
    have hright :
        -∫ x, (fderiv ℝ f x 1) * u x ∂(gaussianReal 0 1) ≤
          (∫ x, (fderiv ℝ f x 1) ^ 2 ∂(gaussianReal 0 1)) ^ (1 / 2 : ℝ) *
            (∫ x, u x ^ 2 ∂(gaussianReal 0 1)) ^ (1 / 2 : ℝ) := h_cauchy
    have hroot :
        ((∫ x, (fderiv ℝ f x 1) ^ 2 ∂(gaussianReal 0 1)) ^ (1 / 2 : ℝ) *
            (∫ x, u x ^ 2 ∂(gaussianReal 0 1)) ^ (1 / 2 : ℝ)) ^ 2 ≤
          (∫ x, (fderiv ℝ f x 1) ^ 2 ∂(gaussianReal 0 1)) *
            ∫ x, u x ^ 2 ∂(gaussianReal 0 1) := by
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, mul_pow,
        Real.sq_sqrt h_energy_nonneg, Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg (u x)))]
    have hsquare := mul_self_le_mul_self hnonneg hright
    nlinarith [hsquare, hroot]
  nlinarith

end RegularityStructures

end
