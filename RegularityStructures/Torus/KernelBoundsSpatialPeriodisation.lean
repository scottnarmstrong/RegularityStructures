/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.KernelBoundsSpatialDerivative
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.PSeries

/-!
# Summable lattice majorants for spatial Gaussian derivatives

The derivative of a one-dimensional Gaussian is rapidly decreasing.  For the torus chart we only
need a polynomially summable majorant on a bounded fundamental interval.  This module records that
majorant in a form suitable for termwise differentiation of the periodisation.
-/

@[expose] public noncomputable section

open Real Set
open scoped ContDiff

namespace RegularityStructures

theorem summable_pi_fin3_prod_of {u : Fin 3 → ℤ → ℝ} (hu : ∀ i, Summable (u i))
    (hnu : ∀ i n, 0 ≤ u i n) :
    Summable (fun k : Fin 3 → ℤ => ∏ i, u i (k i)) := by
  classical
  have h01 : Summable (fun p : ℤ × ℤ => u 0 p.1 * u 1 p.2) :=
    (hu 0).mul_of_nonneg (hu 1) (by intro; exact hnu 0 _) (by intro; exact hnu 1 _)
  have h012 : Summable (fun q : (ℤ × ℤ) × ℤ =>
      (u 0 q.1.1 * u 1 q.1.2) * u 2 q.2) :=
    h01.mul_of_nonneg (hu 2)
      (by intro q; exact mul_nonneg (hnu 0 _) (hnu 1 _)) (by intro; exact hnu 2 _)
  let e2 : (ℤ × ℤ) ≃ (Fin 2 → ℤ) :=
    (piFinTwoEquiv (fun _ : Fin 2 => ℤ)).symm
  let e3 : ((ℤ × ℤ) × ℤ) ≃ (Fin 3 → ℤ) :=
    ((Equiv.prodAssoc ℤ ℤ ℤ).trans
      (Equiv.prodCongr (Equiv.refl ℤ) e2)).trans
      (Fin.consEquiv (fun _ : Fin 3 => ℤ))
  rw [← e3.summable_iff]
  convert h012 using 1
  funext q
  simp [e3, e2, Fin.prod_univ_succ, piFinTwoEquiv]
  ring

def gaussianDerivativeMajorant (B₀ B₁ : ℝ) (M : ℕ) (k : ℤ) : ℝ :=
  B₀ * (if k = 0 then 1 else 0) + B₁ * |(k : ℝ)| ^ (-(M : ℝ))

theorem summable_gaussianDerivativeMajorant {B₀ B₁ : ℝ} {M : ℕ} (hM : 1 < M) :
    Summable (gaussianDerivativeMajorant B₀ B₁ M) := by
  unfold gaussianDerivativeMajorant
  apply Summable.add
  · apply summable_of_ne_finset_zero (s := ({0} : Finset ℤ))
    intro k hk
    have hk0 : k ≠ 0 := by simpa using hk
    simp [hk0]
  · exact (Real.summable_abs_int_rpow (show (1 : ℝ) < M by exact_mod_cast hM)).mul_left B₁

theorem gaussianDerivativeMajorant_nonneg {B₀ B₁ : ℝ} (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁)
    (M : ℕ) (k : ℤ) : 0 ≤ gaussianDerivativeMajorant B₀ B₁ M k := by
  unfold gaussianDerivativeMajorant
  positivity

def gaussKernelSpaceLine (t : ℝ) (i : Fin 3) (y : Fin 3 → ℝ) (k : Fin 3 → ℤ) (s : ℝ) : ℝ :=
  gaussKernel t (Function.update y i s + fun j => (k j : ℝ))

def gaussKernelSpaceLineCoeff (t : ℝ) (i : Fin 3) (y : Fin 3 → ℝ) (k : Fin 3 → ℤ) : ℝ :=
  (4 * π * t) ^ (-(3 : ℝ) / 2) *
    ∏ j, if j = i then 1 else exp (-(4 * t)⁻¹ * (y j + (k j : ℝ)) ^ 2)

theorem contDiff_gaussKernelSpaceLine (t : ℝ) (i : Fin 3) (y : Fin 3 → ℝ)
    (k : Fin 3 → ℤ) : ContDiff ℝ ∞ (gaussKernelSpaceLine t i y k) := by
  fin_cases i
  · have heq : gaussKernelSpaceLine t 0 y k = fun r =>
        gaussKernelSpaceLineCoeff t 0 y k * expPowFun ((4 * t)⁻¹) 2 (r + (k 0 : ℝ)) := by
      funext r
      simp [gaussKernelSpaceLine, gaussKernelSpaceLineCoeff, gaussKernel_eq_prod,
        Fin.prod_univ_three, Function.update, expPowFun, mul_assoc]
      apply Or.inl
      ring
    change ContDiff ℝ ∞ (gaussKernelSpaceLine t 0 y k)
    rw [heq]
    unfold expPowFun
    fun_prop
  · have heq : gaussKernelSpaceLine t 1 y k = fun r =>
        gaussKernelSpaceLineCoeff t 1 y k * expPowFun ((4 * t)⁻¹) 2 (r + (k 1 : ℝ)) := by
      funext r
      simp [gaussKernelSpaceLine, gaussKernelSpaceLineCoeff, gaussKernel_eq_prod,
        Fin.prod_univ_three, Function.update, expPowFun, mul_assoc]
      apply Or.inl
      ring
    change ContDiff ℝ ∞ (gaussKernelSpaceLine t 1 y k)
    rw [heq]
    unfold expPowFun
    fun_prop
  · have heq : gaussKernelSpaceLine t 2 y k = fun r =>
        gaussKernelSpaceLineCoeff t 2 y k * expPowFun ((4 * t)⁻¹) 2 (r + (k 2 : ℝ)) := by
      funext r
      simp [gaussKernelSpaceLine, gaussKernelSpaceLineCoeff, gaussKernel_eq_prod,
        Fin.prod_univ_three, Function.update, expPowFun, mul_assoc]
    change ContDiff ℝ ∞ (gaussKernelSpaceLine t 2 y k)
    rw [heq]
    unfold expPowFun
    fun_prop

theorem heatKernelLift_spaceLine {t : ℝ} (i : Fin 3) (y : Fin 3 → ℝ) (s : ℝ) :
    heatKernelLift t (Function.update y i s) =
      ∑' k : Fin 3 → ℤ, gaussKernelSpaceLine t i y k s := by
  unfold heatKernelLift gaussKernelSpaceLine
  apply tsum_congr
  intro k
  congr 1

theorem iteratedDeriv_gaussKernelSpaceLine {t : ℝ} (n : ℕ) (i : Fin 3) (y : Fin 3 → ℝ)
    (k : Fin 3 → ℤ) (s : ℝ) :
    iteratedDeriv n (gaussKernelSpaceLine t i y k) s =
      gaussKernelSpaceLineCoeff t i y k *
        iteratedDeriv n (expPowFun ((4 * t)⁻¹) 2) (s + (k i : ℝ)) := by
  fin_cases i
  · have heq : gaussKernelSpaceLine t 0 y k = fun r =>
        gaussKernelSpaceLineCoeff t 0 y k * expPowFun ((4 * t)⁻¹) 2 (r + (k 0 : ℝ)) := by
      funext r
      simp [gaussKernelSpaceLine, gaussKernelSpaceLineCoeff, gaussKernel_eq_prod,
        Fin.prod_univ_three, Function.update, expPowFun, mul_assoc]
      apply Or.inl
      ring
    change iteratedDeriv n (gaussKernelSpaceLine t 0 y k) s =
      gaussKernelSpaceLineCoeff t 0 y k *
        iteratedDeriv n (expPowFun ((4 * t)⁻¹) 2) (s + (k 0 : ℝ))
    rw [heq, iteratedDeriv_const_mul_field, iteratedDeriv_comp_add_const]
  · have heq : gaussKernelSpaceLine t 1 y k = fun r =>
        gaussKernelSpaceLineCoeff t 1 y k * expPowFun ((4 * t)⁻¹) 2 (r + (k 1 : ℝ)) := by
      funext r
      simp [gaussKernelSpaceLine, gaussKernelSpaceLineCoeff, gaussKernel_eq_prod,
        Fin.prod_univ_three, Function.update, expPowFun, mul_assoc]
      apply Or.inl
      ring
    change iteratedDeriv n (gaussKernelSpaceLine t 1 y k) s =
      gaussKernelSpaceLineCoeff t 1 y k *
        iteratedDeriv n (expPowFun ((4 * t)⁻¹) 2) (s + (k 1 : ℝ))
    rw [heq, iteratedDeriv_const_mul_field, iteratedDeriv_comp_add_const]
  · have heq : gaussKernelSpaceLine t 2 y k = fun r =>
        gaussKernelSpaceLineCoeff t 2 y k * expPowFun ((4 * t)⁻¹) 2 (r + (k 2 : ℝ)) := by
      funext r
      simp [gaussKernelSpaceLine, gaussKernelSpaceLineCoeff, gaussKernel_eq_prod,
        Fin.prod_univ_three, Function.update, expPowFun, mul_assoc]
    change iteratedDeriv n (gaussKernelSpaceLine t 2 y k) s =
      gaussKernelSpaceLineCoeff t 2 y k *
        iteratedDeriv n (expPowFun ((4 * t)⁻¹) 2) (s + (k 2 : ℝ))
    rw [heq, iteratedDeriv_const_mul_field, iteratedDeriv_comp_add_const]

theorem gaussKernelSpaceLine_deriv_le {t : ℝ} (ht : 0 < t) (i : Fin 3) (n : ℕ)
    (y : Fin 3 → ℝ) (k : Fin 3 → ℤ) (s : ℝ)
    {v : ℤ → ℝ}
    (hv : |iteratedDeriv n (expPowFun ((4 * t)⁻¹) 2) (s + (k i : ℝ))| ≤ v (k i))
    (_hs : s ∈ Icc (-3 / 4 : ℝ) (3 / 4))
    (hy : ∀ j, y j ∈ Icc (-1 / 2 : ℝ) (1 / 2)) :
    |iteratedDeriv n (gaussKernelSpaceLine t i y k) s| ≤
      (4 * π * t) ^ (-(3 : ℝ) / 2) *
        ∏ j, if j = i then v (k j) else
          gaussianOneDimMajorant ((4 * t)⁻¹) (k j) := by
  have hc : 0 < (4 * t)⁻¹ := by positivity
  have hpref : 0 ≤ (4 * π * t) ^ (-(3 : ℝ) / 2) := by positivity
  fin_cases i
  · rw [iteratedDeriv_gaussKernelSpaceLine]
    rw [abs_mul]
    have h1 := gaussian_exp_shift_le_majorant (a := (4 * t)⁻¹) (b := y 1) hc (by
      have := hy 1
      exact ⟨by linarith [this.1], by linarith [this.2]⟩) (k 1)
    have h2 := gaussian_exp_shift_le_majorant (a := (4 * t)⁻¹) (b := y 2) hc (by
      have := hy 2
      exact ⟨by linarith [this.1], by linarith [this.2]⟩) (k 2)
    have hparam : (4 * t)⁻¹ = t⁻¹ * 4⁻¹ := by field_simp
    have h1' : exp (-(t⁻¹ * 4⁻¹ * (y 1 + (k 1 : ℝ)) ^ 2)) ≤
        gaussianOneDimMajorant (t⁻¹ * 4⁻¹) (k 1) := by
      rw [hparam] at h1
      convert h1 using 1
      congr 1
      ring
    have h2' : exp (-(t⁻¹ * 4⁻¹ * (y 2 + (k 2 : ℝ)) ^ 2)) ≤
        gaussianOneDimMajorant (t⁻¹ * 4⁻¹) (k 2) := by
      rw [hparam] at h2
      convert h2 using 1
      congr 1
      ring
    have hcoeff : |gaussKernelSpaceLineCoeff t 0 y k| ≤
        (4 * π * t) ^ (-(3 : ℝ) / 2) *
          (gaussianOneDimMajorant ((4 * t)⁻¹) (k 1) *
            gaussianOneDimMajorant ((4 * t)⁻¹) (k 2)) := by
      have hcoeff0 : 0 ≤ gaussKernelSpaceLineCoeff t 0 y k := by
        unfold gaussKernelSpaceLineCoeff
        positivity
      rw [abs_of_nonneg hcoeff0]
      simp [gaussKernelSpaceLineCoeff, Fin.prod_univ_three]
      gcongr
      · exact gaussianOneDimMajorant_nonneg (a := t⁻¹ * 4⁻¹) _
    have hM1 : 0 ≤ gaussianOneDimMajorant ((4 * t)⁻¹) (k 1) :=
      gaussianOneDimMajorant_nonneg (a := (4 * t)⁻¹) _
    have hM2 : 0 ≤ gaussianOneDimMajorant ((4 * t)⁻¹) (k 2) :=
      gaussianOneDimMajorant_nonneg (a := (4 * t)⁻¹) _
    calc
      |gaussKernelSpaceLineCoeff t 0 y k| *
          |iteratedDeriv n (expPowFun ((4 * t)⁻¹) 2) (s + (k 0 : ℝ))| ≤
          ((4 * π * t) ^ (-(3 : ℝ) / 2) *
            (gaussianOneDimMajorant ((4 * t)⁻¹) (k 1) *
              gaussianOneDimMajorant ((4 * t)⁻¹) (k 2))) *
            |iteratedDeriv n (expPowFun ((4 * t)⁻¹) 2) (s + (k 0 : ℝ))| :=
        mul_le_mul_of_nonneg_right hcoeff (abs_nonneg _)
      _ ≤ (4 * π * t) ^ (-(3 : ℝ) / 2) *
          (v (k 0) * (gaussianOneDimMajorant ((4 * t)⁻¹) (k 1) *
            gaussianOneDimMajorant ((4 * t)⁻¹) (k 2))) := by
        calc
          _ = (4 * π * t) ^ (-(3 : ℝ) / 2) *
              ((gaussianOneDimMajorant ((4 * t)⁻¹) (k 1) *
                gaussianOneDimMajorant ((4 * t)⁻¹) (k 2)) *
                |iteratedDeriv n (expPowFun ((4 * t)⁻¹) 2) (s + (k 0 : ℝ))|) := by ring
          _ ≤ (4 * π * t) ^ (-(3 : ℝ) / 2) *
              ((gaussianOneDimMajorant ((4 * t)⁻¹) (k 1) *
                gaussianOneDimMajorant ((4 * t)⁻¹) (k 2)) * v (k 0)) := by
            gcongr
            exact hv
          _ = _ := by ring
      _ = (4 * π * t) ^ (-(3 : ℝ) / 2) *
          ∏ j, if j = (0 : Fin 3) then v (k j) else
            gaussianOneDimMajorant ((4 * t)⁻¹) (k j) := by
        simp [Fin.prod_univ_three]
        apply Or.inl
        ring
  · rw [iteratedDeriv_gaussKernelSpaceLine]
    rw [abs_mul]
    have h0 := gaussian_exp_shift_le_majorant (a := (4 * t)⁻¹) (b := y 0) hc (by
      have := hy 0
      exact ⟨by linarith [this.1], by linarith [this.2]⟩) (k 0)
    have h2 := gaussian_exp_shift_le_majorant (a := (4 * t)⁻¹) (b := y 2) hc (by
      have := hy 2
      exact ⟨by linarith [this.1], by linarith [this.2]⟩) (k 2)
    have hparam : (4 * t)⁻¹ = t⁻¹ * 4⁻¹ := by field_simp
    have h0' : exp (-(t⁻¹ * 4⁻¹ * (y 0 + (k 0 : ℝ)) ^ 2)) ≤
        gaussianOneDimMajorant (t⁻¹ * 4⁻¹) (k 0) := by
      rw [hparam] at h0
      convert h0 using 1
      congr 1
      ring
    have h2' : exp (-(t⁻¹ * 4⁻¹ * (y 2 + (k 2 : ℝ)) ^ 2)) ≤
        gaussianOneDimMajorant (t⁻¹ * 4⁻¹) (k 2) := by
      rw [hparam] at h2
      convert h2 using 1
      congr 1
      ring
    have hcoeff : |gaussKernelSpaceLineCoeff t 1 y k| ≤
        (4 * π * t) ^ (-(3 : ℝ) / 2) *
          (gaussianOneDimMajorant ((4 * t)⁻¹) (k 0) *
            gaussianOneDimMajorant ((4 * t)⁻¹) (k 2)) := by
      have hcoeff0 : 0 ≤ gaussKernelSpaceLineCoeff t 1 y k := by
        unfold gaussKernelSpaceLineCoeff
        positivity
      rw [abs_of_nonneg hcoeff0]
      simp [gaussKernelSpaceLineCoeff, Fin.prod_univ_three]
      gcongr
      · exact gaussianOneDimMajorant_nonneg (a := t⁻¹ * 4⁻¹) _
    have hM0 : 0 ≤ gaussianOneDimMajorant ((4 * t)⁻¹) (k 0) :=
      gaussianOneDimMajorant_nonneg (a := (4 * t)⁻¹) _
    have hM2 : 0 ≤ gaussianOneDimMajorant ((4 * t)⁻¹) (k 2) :=
      gaussianOneDimMajorant_nonneg (a := (4 * t)⁻¹) _
    calc
      |gaussKernelSpaceLineCoeff t 1 y k| *
          |iteratedDeriv n (expPowFun ((4 * t)⁻¹) 2) (s + (k 1 : ℝ))| ≤
          ((4 * π * t) ^ (-(3 : ℝ) / 2) *
            (gaussianOneDimMajorant ((4 * t)⁻¹) (k 0) *
              gaussianOneDimMajorant ((4 * t)⁻¹) (k 2))) *
            |iteratedDeriv n (expPowFun ((4 * t)⁻¹) 2) (s + (k 1 : ℝ))| :=
        mul_le_mul_of_nonneg_right hcoeff (abs_nonneg _)
      _ ≤ (4 * π * t) ^ (-(3 : ℝ) / 2) *
          (v (k 1) * (gaussianOneDimMajorant ((4 * t)⁻¹) (k 0) *
            gaussianOneDimMajorant ((4 * t)⁻¹) (k 2))) := by
        calc
          _ = (4 * π * t) ^ (-(3 : ℝ) / 2) *
              ((gaussianOneDimMajorant ((4 * t)⁻¹) (k 0) *
                gaussianOneDimMajorant ((4 * t)⁻¹) (k 2)) *
                |iteratedDeriv n (expPowFun ((4 * t)⁻¹) 2) (s + (k 1 : ℝ))|) := by ring
          _ ≤ (4 * π * t) ^ (-(3 : ℝ) / 2) *
              ((gaussianOneDimMajorant ((4 * t)⁻¹) (k 0) *
                gaussianOneDimMajorant ((4 * t)⁻¹) (k 2)) * v (k 1)) := by
            gcongr
            exact hv
          _ = _ := by ring
      _ = (4 * π * t) ^ (-(3 : ℝ) / 2) *
          ∏ j, if j = (1 : Fin 3) then v (k j) else
            gaussianOneDimMajorant ((4 * t)⁻¹) (k j) := by
        simp [Fin.prod_univ_three]
        apply Or.inl
        ring
  · rw [iteratedDeriv_gaussKernelSpaceLine]
    rw [abs_mul]
    have h0 := gaussian_exp_shift_le_majorant (a := (4 * t)⁻¹) (b := y 0) hc (by
      have := hy 0
      exact ⟨by linarith [this.1], by linarith [this.2]⟩) (k 0)
    have h1 := gaussian_exp_shift_le_majorant (a := (4 * t)⁻¹) (b := y 1) hc (by
      have := hy 1
      exact ⟨by linarith [this.1], by linarith [this.2]⟩) (k 1)
    have hparam : (4 * t)⁻¹ = t⁻¹ * 4⁻¹ := by field_simp
    have h0' : exp (-(t⁻¹ * 4⁻¹ * (y 0 + (k 0 : ℝ)) ^ 2)) ≤
        gaussianOneDimMajorant (t⁻¹ * 4⁻¹) (k 0) := by
      rw [hparam] at h0
      convert h0 using 1
      congr 1
      ring
    have h1' : exp (-(t⁻¹ * 4⁻¹ * (y 1 + (k 1 : ℝ)) ^ 2)) ≤
        gaussianOneDimMajorant (t⁻¹ * 4⁻¹) (k 1) := by
      rw [hparam] at h1
      convert h1 using 1
      congr 1
      ring
    have hcoeff : |gaussKernelSpaceLineCoeff t 2 y k| ≤
        (4 * π * t) ^ (-(3 : ℝ) / 2) *
          (gaussianOneDimMajorant ((4 * t)⁻¹) (k 0) *
            gaussianOneDimMajorant ((4 * t)⁻¹) (k 1)) := by
      have hcoeff0 : 0 ≤ gaussKernelSpaceLineCoeff t 2 y k := by
        unfold gaussKernelSpaceLineCoeff
        positivity
      rw [abs_of_nonneg hcoeff0]
      simp [gaussKernelSpaceLineCoeff, Fin.prod_univ_three]
      gcongr
      · exact gaussianOneDimMajorant_nonneg (a := t⁻¹ * 4⁻¹) _
    have hM0 : 0 ≤ gaussianOneDimMajorant ((4 * t)⁻¹) (k 0) :=
      gaussianOneDimMajorant_nonneg (a := (4 * t)⁻¹) _
    have hM1 : 0 ≤ gaussianOneDimMajorant ((4 * t)⁻¹) (k 1) :=
      gaussianOneDimMajorant_nonneg (a := (4 * t)⁻¹) _
    calc
      |gaussKernelSpaceLineCoeff t 2 y k| *
          |iteratedDeriv n (expPowFun ((4 * t)⁻¹) 2) (s + (k 2 : ℝ))| ≤
          ((4 * π * t) ^ (-(3 : ℝ) / 2) *
            (gaussianOneDimMajorant ((4 * t)⁻¹) (k 0) *
              gaussianOneDimMajorant ((4 * t)⁻¹) (k 1))) *
            |iteratedDeriv n (expPowFun ((4 * t)⁻¹) 2) (s + (k 2 : ℝ))| :=
        mul_le_mul_of_nonneg_right hcoeff (abs_nonneg _)
      _ ≤ (4 * π * t) ^ (-(3 : ℝ) / 2) *
          (v (k 2) * (gaussianOneDimMajorant ((4 * t)⁻¹) (k 0) *
            gaussianOneDimMajorant ((4 * t)⁻¹) (k 1))) := by
        calc
          _ = (4 * π * t) ^ (-(3 : ℝ) / 2) *
              ((gaussianOneDimMajorant ((4 * t)⁻¹) (k 0) *
                gaussianOneDimMajorant ((4 * t)⁻¹) (k 1)) *
                |iteratedDeriv n (expPowFun ((4 * t)⁻¹) 2) (s + (k 2 : ℝ))|) := by ring
          _ ≤ (4 * π * t) ^ (-(3 : ℝ) / 2) *
              ((gaussianOneDimMajorant ((4 * t)⁻¹) (k 0) *
                gaussianOneDimMajorant ((4 * t)⁻¹) (k 1)) * v (k 2)) := by
            gcongr
            exact hv
          _ = _ := by ring
      _ = (4 * π * t) ^ (-(3 : ℝ) / 2) *
          ∏ j, if j = (2 : Fin 3) then v (k j) else
            gaussianOneDimMajorant ((4 * t)⁻¹) (k j) := by
        simp [Fin.prod_univ_three]
        apply Or.inl
        ring

private theorem one_le_abs_int_cast {k : ℤ} (hk : k ≠ 0) :
    (1 : ℝ) ≤ |(k : ℝ)| := by
  rcases lt_or_gt_of_ne hk with hkneg | hkpos
  · rw [abs_of_neg (by exact_mod_cast hkneg : (k : ℝ) < 0)]
    have hk' : (1 : ℤ) ≤ -k := by omega
    exact_mod_cast hk'
  · rw [abs_of_pos (by exact_mod_cast hkpos : (0 : ℝ) < k)]
    have hk' : (1 : ℤ) ≤ k := by omega
    exact_mod_cast hk'

private theorem abs_add_int_lower {y : ℝ} {k : ℤ} (hy : y ∈ Icc (-3 / 4 : ℝ) (3 / 4))
    (hk : k ≠ 0) : |(k : ℝ)| / 4 ≤ |y + k| := by
  have hkabs : (1 : ℝ) ≤ |(k : ℝ)| := one_le_abs_int_cast hk
  have htriangle : |(k : ℝ)| ≤ |y + k| + |y| := by
    calc
      |(k : ℝ)| = |(y + (k : ℝ)) - y| := by
        congr 1
        ring
      _ ≤ |y + (k : ℝ)| + |y| := by
        simpa [sub_eq_add_neg] using abs_add_le (y + (k : ℝ)) (-y)
  have hyabs : |y| ≤ (3 : ℝ) / 4 := by
    rw [abs_le]
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  linarith

theorem exists_gaussian_derivative_lattice_majorant {c : ℝ} (hc : 0 < c) (n : ℕ) :
    ∃ v : ℤ → ℝ, Summable v ∧ (∀ k, 0 ≤ v k) ∧
      ∀ y ∈ Icc (-3 / 4 : ℝ) (3 / 4), ∀ k : ℤ,
        |iteratedDeriv n (expPowFun c 2) (y + k)| ≤ v k := by
  obtain ⟨B₀, hB₀⟩ := exists_bound_iteratedDeriv_expPowFun hc (j := 1) one_pos n
  obtain ⟨B₂, hB₂⟩ := exists_bound_abs_pow_mul_iteratedDeriv_expPowFun hc
    (j := 1) one_pos 2 n
  let C₀ := max B₀ 0
  let C₂ := max B₂ 0
  let v := gaussianDerivativeMajorant C₀ (C₂ * 4 ^ (2 : ℝ)) 2
  refine ⟨v, ?_, ?_, ?_⟩
  · exact summable_gaussianDerivativeMajorant (B₀ := C₀) (B₁ := C₂ * 4 ^ (2 : ℝ))
      (M := 2) (by norm_num)
  · intro k
    exact gaussianDerivativeMajorant_nonneg (le_max_right B₀ 0)
      (mul_nonneg (le_max_right B₂ 0) (by positivity)) 2 k
  · intro y hy k
    by_cases hk : k = 0
    · subst k
      calc
        |iteratedDeriv n (expPowFun c 2) (y + (0 : ℤ))| =
            |iteratedDeriv n (expPowFun c 2) y| := by simp
        _ ≤ C₀ := by
          simpa [C₀] using (hB₀ y).trans (le_max_left B₀ 0)
        _ = v 0 := by simp [v, gaussianDerivativeMajorant]
    · have hkcast : (k : ℝ) ≠ 0 := by exact_mod_cast hk
      have hkabs : 0 < |(k : ℝ)| := abs_pos.mpr hkcast
      have hxy : 0 < |y + (k : ℝ)| := by
        have hlow := abs_add_int_lower hy hk
        exact lt_of_lt_of_le (by positivity) hlow
      have hpow : (|(k : ℝ)| / 4) ^ (2 : ℕ) ≤ |y + (k : ℝ)| ^ (2 : ℕ) := by
        have hlow := abs_add_int_lower hy hk
        nlinarith [sq_nonneg (|y + (k : ℝ)| - |(k : ℝ)| / 2),
          abs_nonneg (y + (k : ℝ)), abs_nonneg (k : ℝ)]
      have hweighted : |y + (k : ℝ)| ^ (2 : ℕ) *
          |iteratedDeriv n (expPowFun c 2) (y + k)| ≤ C₂ := by
        simpa [C₂] using (hB₂ (y + k)).trans (le_max_left B₂ 0)
      have hdiv : |iteratedDeriv n (expPowFun c 2) (y + k)| ≤
          C₂ / (|(k : ℝ)| / 4) ^ (2 : ℕ) := by
        apply (le_div_iff₀ (by positivity)).2
        calc
          |iteratedDeriv n (expPowFun c 2) (y + k)| *
              (|(k : ℝ)| / 4) ^ (2 : ℕ) =
              (|(k : ℝ)| / 4) ^ (2 : ℕ) *
                |iteratedDeriv n (expPowFun c 2) (y + k)| := by ring
          _ ≤ |y + (k : ℝ)| ^ (2 : ℕ) *
                |iteratedDeriv n (expPowFun c 2) (y + k)| :=
            mul_le_mul_of_nonneg_right hpow (abs_nonneg _)
          _ ≤ C₂ := hweighted
      have hrewrite : C₂ / (|(k : ℝ)| / 4) ^ (2 : ℕ) =
          C₂ * 4 ^ (2 : ℝ) * |(k : ℝ)| ^ (-(2 : ℝ)) := by
        have hkpow : |(k : ℝ)| ^ (-(2 : ℝ)) = (|(k : ℝ)| ^ (2 : ℕ))⁻¹ := by
          exact (Real.rpow_neg (abs_nonneg _) 2).trans
            (congrArg Inv.inv (Real.rpow_natCast |(k : ℝ)| 2))
        rw [hkpow]
        field_simp [ne_of_gt hkabs]
        ring
      calc
        |iteratedDeriv n (expPowFun c 2) (y + k)| ≤
            C₂ / (|(k : ℝ)| / 4) ^ (2 : ℕ) := hdiv
        _ = C₂ * 4 ^ (2 : ℝ) * |(k : ℝ)| ^ (-(2 : ℝ)) := by
          exact hrewrite
        _ = v k := by simp [v, gaussianDerivativeMajorant, hk]

def gaussianSpaceDerivativeFactor (t : ℝ) (i : Fin 3) (v : ℤ → ℝ)
    (j : Fin 3) (n : ℤ) : ℝ :=
  if j = i then v n else gaussianOneDimMajorant ((4 * t)⁻¹) n

def gaussianSpaceDerivativeMajorant (t : ℝ) (i : Fin 3) (v : ℤ → ℝ)
    (k : Fin 3 → ℤ) : ℝ :=
  (4 * π * t) ^ (-(3 : ℝ) / 2) *
    ∏ j, gaussianSpaceDerivativeFactor t i v j (k j)

theorem summable_gaussianSpaceDerivativeMajorant {t : ℝ} (ht : 0 < t) (i : Fin 3)
    {v : ℤ → ℝ} (hvsum : Summable v) (hvnonneg : ∀ n, 0 ≤ v n) :
    Summable (gaussianSpaceDerivativeMajorant t i v) := by
  have hfac : ∀ j, Summable (fun n : ℤ =>
      gaussianSpaceDerivativeFactor t i v j n) := by
    intro j
    by_cases hji : j = i
    · simpa [gaussianSpaceDerivativeFactor, hji] using hvsum
    · simpa [gaussianSpaceDerivativeFactor, hji] using
        summable_gaussianOneDimMajorant (a := (4 * t)⁻¹) (by positivity)
  have hfac_nonneg : ∀ j n, 0 ≤
      gaussianSpaceDerivativeFactor t i v j n := by
    intro j n
    by_cases hji : j = i
    · simp [gaussianSpaceDerivativeFactor, hji, hvnonneg n]
    · simp [gaussianSpaceDerivativeFactor, hji, gaussianOneDimMajorant_nonneg]
  have hprod : Summable (fun k : Fin 3 → ℤ =>
      ∏ j, gaussianSpaceDerivativeFactor t i v j (k j)) :=
    summable_pi_fin3_prod_of hfac hfac_nonneg
  exact hprod.mul_left ((4 * π * t) ^ (-(3 : ℝ) / 2))

theorem exists_gaussKernelSpaceLine_derivative_majorant {t : ℝ} (ht : 0 < t) (i : Fin 3)
    (n : ℕ) (y : Fin 3 → ℝ) (hy : ∀ j, y j ∈ Icc (-1 / 2 : ℝ) (1 / 2)) :
    ∃ u : (Fin 3 → ℤ) → ℝ, Summable u ∧
      ∀ (k : Fin 3 → ℤ) (s : ℝ), s ∈ Ioo (-3 / 4 : ℝ) (3 / 4) →
        ‖iteratedDeriv n (gaussKernelSpaceLine t i y k) s‖ ≤ u k := by
  obtain ⟨v, hvsum, hvnonneg, hvbound⟩ :=
    exists_gaussian_derivative_lattice_majorant (c := (4 * t)⁻¹) (by positivity) n
  refine ⟨gaussianSpaceDerivativeMajorant t i v,
    summable_gaussianSpaceDerivativeMajorant ht i hvsum hvnonneg, ?_⟩
  intro k s hs
  have hline := gaussKernelSpaceLine_deriv_le (t := t) ht i n y k s (v := v)
    (hvbound s ⟨le_of_lt hs.1, le_of_lt hs.2⟩ (k i))
      ⟨le_of_lt hs.1, le_of_lt hs.2⟩ hy
  simpa [gaussianSpaceDerivativeMajorant, gaussianSpaceDerivativeFactor, norm_eq_abs] using hline

theorem summable_heatKernelLift_spaceLine {t : ℝ} (ht : 0 < t) (i : Fin 3)
    (y : Fin 3 → ℝ) (hy : ∀ j, y j ∈ Icc (-1 / 2 : ℝ) (1 / 2)) :
    Summable (fun k : Fin 3 → ℤ => gaussKernelSpaceLine t i y k (y i)) := by
  have hy12 : ∀ j, y j ∈ Icc (-1 : ℝ) 2 := by
    intro j
    exact ⟨by linarith [(hy j).1], by linarith [(hy j).2]⟩
  apply Summable.of_norm_bounded (summable_gaussian_vector_majorant ht)
  intro k
  simpa [gaussKernelSpaceLine, Function.update] using
    (gaussKernel_le_uniform_majorant ht hy12 k)

theorem hasDerivAt_tsum_gaussKernelSpaceLine_iterated {t : ℝ} (ht : 0 < t) (i : Fin 3)
    (n : ℕ) (y : Fin 3 → ℝ) (hy : ∀ j, y j ∈ Icc (-1 / 2 : ℝ) (1 / 2)) :
    HasDerivAt (fun s => ∑' k : Fin 3 → ℤ,
        iteratedDeriv n (gaussKernelSpaceLine t i y k) s)
      (∑' k : Fin 3 → ℤ,
        iteratedDeriv (n + 1) (gaussKernelSpaceLine t i y k) (y i)) (y i) := by
  obtain ⟨u₀, hu₀, hu_bound₀⟩ := exists_gaussKernelSpaceLine_derivative_majorant ht i n y hy
  obtain ⟨u₁, hu₁, hu_bound₁⟩ :=
    exists_gaussKernelSpaceLine_derivative_majorant ht i (n + 1) y hy
  have hy0 : y i ∈ Ioo (-3 / 4 : ℝ) (3 / 4) := by
    exact ⟨by linarith [(hy i).1], by linarith [(hy i).2]⟩
  have hg0 : Summable (fun k : Fin 3 → ℤ =>
      iteratedDeriv n (gaussKernelSpaceLine t i y k) (y i)) := by
    apply Summable.of_norm_bounded hu₀
    intro k
    exact hu_bound₀ k (y i) hy0
  apply hasDerivAt_tsum_of_isPreconnected (y₀ := y i) (y := y i) hu₁ isOpen_Ioo
    isPreconnected_Ioo
  · intro k s hs
    simpa only [iteratedDeriv_succ] using
      ((contDiff_gaussKernelSpaceLine t i y k).differentiable_iteratedDeriv n
        (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n) s).hasDerivAt
  · exact hu_bound₁
  · exact hy0
  · exact hg0
  · exact hy0

theorem summable_heatKernelLift_spaceLine_iterated {t : ℝ} (ht : 0 < t) (i : Fin 3)
    (n : ℕ) (y : Fin 3 → ℝ) (hy : ∀ j, y j ∈ Icc (-1 / 2 : ℝ) (1 / 2)) :
    Summable (fun k : Fin 3 → ℤ =>
      iteratedDeriv n (gaussKernelSpaceLine t i y k) (y i)) := by
  obtain ⟨u, hu, hu_bound⟩ := exists_gaussKernelSpaceLine_derivative_majorant ht i n y hy
  apply Summable.of_norm_bounded hu
  intro k
  exact hu_bound k (y i) ⟨by linarith [(hy i).1], by linarith [(hy i).2]⟩

theorem hasDerivAt_heatKernelLift_spaceLine {t : ℝ} (ht : 0 < t) (i : Fin 3)
    (y : Fin 3 → ℝ) (hy : ∀ j, y j ∈ Icc (-1 / 2 : ℝ) (1 / 2)) :
    HasDerivAt (fun s => heatKernelLift t (Function.update y i s))
      (∑' k : Fin 3 → ℤ, iteratedDeriv 1 (gaussKernelSpaceLine t i y k) (y i)) (y i) := by
  have hfun : (fun s => heatKernelLift t (Function.update y i s)) =
      (fun s => ∑' k : Fin 3 → ℤ, gaussKernelSpaceLine t i y k s) := by
    funext s
    exact heatKernelLift_spaceLine i y s
  rw [hfun]
  simpa only [iteratedDeriv_zero, zero_add] using
    hasDerivAt_tsum_gaussKernelSpaceLine_iterated ht i 0 y hy

theorem iteratedDeriv_two_expPowFun (c x : ℝ) :
    iteratedDeriv 2 (expPowFun c 2) x =
      (4 * c ^ 2 * x ^ 2 - 2 * c) * expPowFun c 2 x := by
  have h₁ : deriv (expPowFun c 2) = fun r =>
      -(c * 2 * r) * expPowFun c 2 r := by
    funext r
    simpa using (hasDerivAt_expPowFun c 2 r).deriv
  have h₂ := (((hasDerivAt_id x).const_mul (-(c * 2))).mul
    (hasDerivAt_expPowFun c 2 x)).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, h₁]
  have heq : (fun r => -(c * 2 * r) * expPowFun c 2 r) =
      (fun r => -(c * 2 * r)) * expPowFun c 2 := by
    funext r
    rfl
  rw [heq]
  convert h₂ using 1
  · congr 1
    funext r
    simp [id]
  · simp [id]
    ring

theorem hasDerivAt_gaussKernel_time_explicit {t : ℝ} (ht : 0 < t) (y : Fin 3 → ℝ) :
    HasDerivAt (fun s => gaussKernel s y)
      (((4 * π) * (-(3 : ℝ) / 2) * (4 * π * t) ^ (-(3 : ℝ) / 2 - 1)) *
          exp (-sqNorm3 y / (4 * t)) +
        (4 * π * t) ^ (-(3 : ℝ) / 2) *
          (exp (-sqNorm3 y / (4 * t)) * (4 * sqNorm3 y / (4 * t) ^ 2))) t := by
  have hbase : HasDerivAt (fun s : ℝ => (4 * π * s) ^ (-(3 : ℝ) / 2))
      ((4 * π) * (-(3 : ℝ) / 2) * (4 * π * t) ^ (-(3 : ℝ) / 2 - 1)) t := by
    have h := ((hasDerivAt_id t).const_mul (4 * π)).rpow_const
      (p := -(3 : ℝ) / 2)
      (Or.inl (by positivity : (4 * π * t : ℝ) ≠ 0))
    convert h using 1
    · funext s
      simp [id]
    · simp [id]
  have harg : HasDerivAt (fun s : ℝ => -sqNorm3 y / (4 * s))
      (4 * sqNorm3 y / (4 * t) ^ 2) t := by
    have h := (hasDerivAt_const t (-sqNorm3 y)).div
      ((hasDerivAt_id t).const_mul (4 : ℝ)) (by positivity : (4 * t : ℝ) ≠ 0)
    convert h using 1
    · funext s
      simp [id]
    · simp [id]
      ring
  have h := hbase.mul harg.exp
  unfold gaussKernel
  convert h using 1

theorem gaussKernel_space_second_eq {t : ℝ} (i : Fin 3) (y : Fin 3 → ℝ) :
    iteratedDeriv 2 (gaussKernelSpaceLine t i y (fun _ : Fin 3 => (0 : ℤ))) (y i) =
      gaussKernel t y *
        (4 * ((4 * t)⁻¹) ^ 2 * (y i) ^ 2 - 2 * ((4 * t)⁻¹)) := by
  fin_cases i
  · rw [iteratedDeriv_gaussKernelSpaceLine, iteratedDeriv_two_expPowFun]
    simp [gaussKernelSpaceLineCoeff, gaussKernel_eq_prod,
      expPowFun, Fin.prod_univ_three]
    ring
  · rw [iteratedDeriv_gaussKernelSpaceLine, iteratedDeriv_two_expPowFun]
    simp [gaussKernelSpaceLineCoeff, gaussKernel_eq_prod,
      expPowFun, Fin.prod_univ_three]
    ring
  · rw [iteratedDeriv_gaussKernelSpaceLine, iteratedDeriv_two_expPowFun]
    simp [gaussKernelSpaceLineCoeff, gaussKernel_eq_prod,
      expPowFun, Fin.prod_univ_three]
    ring

theorem gaussKernel_space_second_eq_lattice {t : ℝ} (i : Fin 3) (y : Fin 3 → ℝ)
    (k : Fin 3 → ℤ) :
    iteratedDeriv 2 (gaussKernelSpaceLine t i y k) (y i) =
      gaussKernel t (y + fun j => (k j : ℝ)) *
        (4 * ((4 * t)⁻¹) ^ 2 * (y i + (k i : ℝ)) ^ 2 - 2 * ((4 * t)⁻¹)) := by
  fin_cases i
  · rw [iteratedDeriv_gaussKernelSpaceLine, iteratedDeriv_two_expPowFun]
    simp [gaussKernelSpaceLineCoeff, gaussKernel_eq_prod, expPowFun,
      Fin.prod_univ_three]
    ring
  · rw [iteratedDeriv_gaussKernelSpaceLine, iteratedDeriv_two_expPowFun]
    simp [gaussKernelSpaceLineCoeff, gaussKernel_eq_prod, expPowFun,
      Fin.prod_univ_three]
    ring
  · rw [iteratedDeriv_gaussKernelSpaceLine, iteratedDeriv_two_expPowFun]
    simp [gaussKernelSpaceLineCoeff, gaussKernel_eq_prod, expPowFun,
      Fin.prod_univ_three]
    ring

theorem gaussKernel_time_deriv_eq_space_second {t : ℝ} (ht : 0 < t) (y : Fin 3 → ℝ) :
    deriv (fun s => gaussKernel s y) t =
      ∑ i : Fin 3, iteratedDeriv 2
        (gaussKernelSpaceLine t i y (fun _ : Fin 3 => (0 : ℤ))) (y i) := by
  rw [(hasDerivAt_gaussKernel_time_explicit ht y).deriv]
  rw [Fin.sum_univ_three, gaussKernel_space_second_eq, gaussKernel_space_second_eq,
    gaussKernel_space_second_eq]
  have hpref : (4 * π) * (-(3 : ℝ) / 2) * (4 * π * t) ^ (-(3 : ℝ) / 2 - 1) =
      (4 * π * t) ^ (-(3 : ℝ) / 2) * (-(3 : ℝ) / (2 * t)) := by
    calc
      (4 * π) * (-(3 : ℝ) / 2) * (4 * π * t) ^ (-(3 : ℝ) / 2 - 1) =
          (4 * π) * (-(3 : ℝ) / 2) *
            ((4 * π * t) ^ (-(3 : ℝ) / 2) * (4 * π * t) ^ (-1 : ℝ)) := by
              rw [show -(3 : ℝ) / 2 - 1 = -(3 : ℝ) / 2 + (-1 : ℝ) by ring,
                Real.rpow_add (by positivity)]
      _ = (4 * π * t) ^ (-(3 : ℝ) / 2) * (-(3 : ℝ) / (2 * t)) := by
        rw [Real.rpow_neg_one]
        field_simp [ne_of_gt (show 0 < 4 * π * t by positivity)]
  rw [hpref]
  simp only [gaussKernel]
  ring_nf
  field_simp [ne_of_gt ht]
  unfold sqNorm3
  rw [Fin.sum_univ_three]
  ring

theorem gaussKernel_lattice_time_deriv_eq_space_second {t : ℝ} (ht : 0 < t)
    (y : Fin 3 → ℝ) (k : Fin 3 → ℤ) :
    deriv (fun s => gaussKernel s (y + fun j => (k j : ℝ))) t =
      ∑ i : Fin 3, iteratedDeriv 2 (gaussKernelSpaceLine t i y k) (y i) := by
  rw [gaussKernel_time_deriv_eq_space_second ht]
  rw [Fin.sum_univ_three, gaussKernel_space_second_eq,
    gaussKernel_space_second_eq, gaussKernel_space_second_eq]
  rw [Fin.sum_univ_three, gaussKernel_space_second_eq_lattice,
    gaussKernel_space_second_eq_lattice, gaussKernel_space_second_eq_lattice]
  simp only [Pi.add_apply]

theorem exists_gaussian_sq_exp_lattice_majorant {a : ℝ} (ha : 0 < a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ Icc (-1 / 2 : ℝ) (1 / 2), ∀ k : ℤ,
      (y + (k : ℝ)) ^ 2 * exp (-a * (y + (k : ℝ)) ^ 2) ≤
        B * gaussianOneDimMajorant (a / 2) k := by
  obtain ⟨B, hB⟩ := exists_bound_abs_pow_mul_expPowFun (c := a / 2) (by positivity)
    (j := 1) one_pos 2
  have hB0 : 0 ≤ B := by
    have h := hB 0
    have hnonneg : 0 ≤ |(0 : ℝ)| ^ 2 * expPowFun (a / 2) 2 0 := by
      simp [expPowFun]
    linarith
  refine ⟨B, hB0, ?_⟩
  intro y hy k
  have hshift := gaussian_exp_shift_le_majorant (a := a / 2) (by positivity)
    (⟨by linarith [hy.1], by linarith [hy.2]⟩ : y ∈ Icc (-1 : ℝ) 2) k
  have hweighted : |y + (k : ℝ)| ^ 2 *
      exp (-(a / 2) * (y + (k : ℝ)) ^ 2) ≤ B := by
    simpa [expPowFun, sq_abs] using hB (y + (k : ℝ))
  calc
    (y + (k : ℝ)) ^ 2 * exp (-a * (y + (k : ℝ)) ^ 2) =
        (|y + (k : ℝ)| ^ 2 * exp (-(a / 2) * (y + (k : ℝ)) ^ 2)) *
          exp (-(a / 2) * (y + (k : ℝ)) ^ 2) := by
      rw [sq_abs]
      calc
        (y + (k : ℝ)) ^ 2 * exp (-a * (y + (k : ℝ)) ^ 2) =
            (y + (k : ℝ)) ^ 2 *
              (exp (-(a / 2) * (y + (k : ℝ)) ^ 2) *
                exp (-(a / 2) * (y + (k : ℝ)) ^ 2)) := by
          congr 1
          rw [← Real.exp_add]
          congr 1
          ring
        _ = ((y + (k : ℝ)) ^ 2 *
              exp (-(a / 2) * (y + (k : ℝ)) ^ 2)) *
            exp (-(a / 2) * (y + (k : ℝ)) ^ 2) := by ring
    _ ≤ B * exp (-(a / 2) * (y + (k : ℝ)) ^ 2) := by
      gcongr
    _ ≤ B * gaussianOneDimMajorant (a / 2) k := by
      gcongr

def gaussianTimeDerivativeFactor (τ B : ℝ) (i j : Fin 3) (n : ℤ) : ℝ :=
  if j = i then B * gaussianOneDimMajorant ((6 * τ)⁻¹ / 2) n
  else gaussianOneDimMajorant (6 * τ)⁻¹ n

def gaussianTimeDerivativeMajorant (τ B : ℝ) (i : Fin 3) (k : Fin 3 → ℤ) : ℝ :=
  (2 * π * τ) ^ (-(3 : ℝ) / 2) *
    (4 * (2 * τ)⁻¹ ^ 2 * ∏ j, gaussianTimeDerivativeFactor τ B i j (k j) +
      2 * (2 * τ)⁻¹ * ∏ j, gaussianOneDimMajorant (6 * τ)⁻¹ (k j))

theorem summable_gaussianTimeDerivativeMajorant {τ B : ℝ} (hτ : 0 < τ) (hB : 0 ≤ B)
    (i : Fin 3) : Summable (gaussianTimeDerivativeMajorant τ B i) := by
  have hfac : ∀ j, Summable (gaussianTimeDerivativeFactor τ B i j) := by
    intro j
    by_cases hji : j = i
    · subst j
      unfold gaussianTimeDerivativeFactor
      simp only [↓reduceIte]
      exact (summable_gaussianOneDimMajorant (a := (6 * τ)⁻¹ / 2) (by positivity)).mul_left B
    · unfold gaussianTimeDerivativeFactor
      simp only [hji, ↓reduceIte]
      exact summable_gaussianOneDimMajorant (a := (6 * τ)⁻¹) (by positivity)
  have hfac_nonneg : ∀ j n, 0 ≤ gaussianTimeDerivativeFactor τ B i j n := by
    intro j n
    by_cases hji : j = i
    · subst j
      unfold gaussianTimeDerivativeFactor
      simp only [↓reduceIte]
      exact mul_nonneg hB (gaussianOneDimMajorant_nonneg _)
    · unfold gaussianTimeDerivativeFactor
      simp only [hji, ↓reduceIte]
      exact gaussianOneDimMajorant_nonneg _
  have hprod₁ : Summable (fun k : Fin 3 → ℤ =>
      ∏ j, gaussianTimeDerivativeFactor τ B i j (k j)) :=
    summable_pi_fin3_prod_of hfac hfac_nonneg
  have hprod₂ : Summable (fun k : Fin 3 → ℤ =>
      ∏ j, gaussianOneDimMajorant (6 * τ)⁻¹ (k j)) :=
    summable_pi_fin3_prod (summable_gaussianOneDimMajorant (by positivity))
      gaussianOneDimMajorant_nonneg
  change Summable (fun k : Fin 3 → ℤ =>
    (2 * π * τ) ^ (-(3 : ℝ) / 2) *
      (4 * (2 * τ)⁻¹ ^ 2 * ∏ j, gaussianTimeDerivativeFactor τ B i j (k j) +
        2 * (2 * τ)⁻¹ * ∏ j, gaussianOneDimMajorant (6 * τ)⁻¹ (k j)))
  have hsum := (hprod₁.mul_left
      ((2 * π * τ) ^ (-(3 : ℝ) / 2) * (4 * (2 * τ)⁻¹ ^ 2))).add
    (hprod₂.mul_left ((2 * π * τ) ^ (-(3 : ℝ) / 2) * (2 * (2 * τ)⁻¹)))
  convert hsum using 1
  funext k
  ring

theorem gaussian_time_interval_bounds {τ s : ℝ} (hτ : 0 < τ)
    (hs : s ∈ Icc (τ / 2) (3 * τ / 2)) :
    0 < s ∧ (6 * τ)⁻¹ ≤ (4 * s)⁻¹ ∧ (4 * s)⁻¹ ≤ (2 * τ)⁻¹ ∧
      (4 * π * s) ^ (-(3 : ℝ) / 2) ≤ (2 * π * τ) ^ (-(3 : ℝ) / 2) := by
  have hspos : 0 < s := by linarith [hs.1, hτ]
  have hlow : 4 * s ≤ 6 * τ := by linarith [hs.2]
  have hupp : 2 * τ ≤ 4 * s := by linarith [hs.1]
  have hinv_low : (6 * τ)⁻¹ ≤ (4 * s)⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le (by positivity : 0 < 4 * s) hlow
  have hinv_upp : (4 * s)⁻¹ ≤ (2 * τ)⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le (by positivity : 0 < 2 * τ) hupp
  have hbase : 0 < 2 * π * τ := by positivity
  have hbase_le : 2 * π * τ ≤ 4 * π * s := by
    nlinarith [Real.pi_pos, hupp]
  refine ⟨hspos, hinv_low, hinv_upp, ?_⟩
  exact Real.rpow_le_rpow_of_nonpos hbase hbase_le (by norm_num)

theorem gaussian_sq_exp_interval_bound {τ s B : ℝ} (hτ : 0 < τ)
    (hs : s ∈ Icc (τ / 2) (3 * τ / 2))
    (hB : ∀ y ∈ Icc (-1 / 2 : ℝ) (1 / 2), ∀ k : ℤ,
      (y + (k : ℝ)) ^ 2 * exp (-(6 * τ)⁻¹ * (y + (k : ℝ)) ^ 2) ≤
        B * gaussianOneDimMajorant ((6 * τ)⁻¹ / 2) k)
    {y : ℝ} (hy : y ∈ Icc (-1 / 2 : ℝ) (1 / 2)) (k : ℤ) :
    (y + (k : ℝ)) ^ 2 * exp (-(4 * s)⁻¹ * (y + (k : ℝ)) ^ 2) ≤
      B * gaussianOneDimMajorant ((6 * τ)⁻¹ / 2) k := by
  have hbounds := gaussian_time_interval_bounds hτ hs
  have hexp : exp (-(4 * s)⁻¹ * (y + (k : ℝ)) ^ 2) ≤
      exp (-(6 * τ)⁻¹ * (y + (k : ℝ)) ^ 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (y + (k : ℝ)), hbounds.2.1]
  calc
    (y + (k : ℝ)) ^ 2 * exp (-(4 * s)⁻¹ * (y + (k : ℝ)) ^ 2) ≤
        (y + (k : ℝ)) ^ 2 * exp (-(6 * τ)⁻¹ * (y + (k : ℝ)) ^ 2) := by
      gcongr
    _ ≤ B * gaussianOneDimMajorant ((6 * τ)⁻¹ / 2) k := hB y hy k

theorem gaussian_exp_interval_bound {τ s : ℝ} (hτ : 0 < τ)
    (hs : s ∈ Icc (τ / 2) (3 * τ / 2)) {y : ℝ}
    (hy : y ∈ Icc (-1 / 2 : ℝ) (1 / 2)) (k : ℤ) :
    exp (-(4 * s)⁻¹ * (y + (k : ℝ)) ^ 2) ≤
      gaussianOneDimMajorant (6 * τ)⁻¹ k := by
  have hbounds := gaussian_time_interval_bounds hτ hs
  have hshift := gaussian_exp_shift_le_majorant (a := (6 * τ)⁻¹) (by positivity)
    (⟨by linarith [hy.1], by linarith [hy.2]⟩ : y ∈ Icc (-1 : ℝ) 2) k
  have hexp : exp (-(4 * s)⁻¹ * (y + (k : ℝ)) ^ 2) ≤
      exp (-(6 * τ)⁻¹ * (y + (k : ℝ)) ^ 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (y + (k : ℝ)), hbounds.2.1]
  exact hexp.trans hshift

theorem gaussKernel_sq_factor_interval_bound {τ s B : ℝ} (hτ : 0 < τ)
    (hs : s ∈ Icc (τ / 2) (3 * τ / 2))
    (hB0 : 0 ≤ B)
    (hB : ∀ y ∈ Icc (-1 / 2 : ℝ) (1 / 2), ∀ k : ℤ,
      (y + (k : ℝ)) ^ 2 * exp (-(6 * τ)⁻¹ * (y + (k : ℝ)) ^ 2) ≤
        B * gaussianOneDimMajorant ((6 * τ)⁻¹ / 2) k)
    (i : Fin 3) (y : Fin 3 → ℝ) (hy : ∀ j, y j ∈ Icc (-1 / 2 : ℝ) (1 / 2))
    (k : Fin 3 → ℤ) :
    gaussKernel s (y + fun j => (k j : ℝ)) * (y i + (k i : ℝ)) ^ 2 ≤
      (2 * π * τ) ^ (-(3 : ℝ) / 2) *
        ∏ j, gaussianTimeDerivativeFactor τ B i j (k j) := by
  have hbounds := gaussian_time_interval_bounds hτ hs
  have hpref : (4 * π * s) ^ (-(3 : ℝ) / 2) ≤
      (2 * π * τ) ^ (-(3 : ℝ) / 2) := hbounds.2.2.2
  fin_cases i
  · have hpoly := gaussian_sq_exp_interval_bound hτ hs hB (hy 0) (k 0)
    have h1 := gaussian_exp_interval_bound hτ hs (hy 1) (k 1)
    have h2 := gaussian_exp_interval_bound hτ hs (hy 2) (k 2)
    have hBmul0 : 0 ≤ B * gaussianOneDimMajorant ((6 * τ)⁻¹ / 2) (k 0) :=
      mul_nonneg hB0 (gaussianOneDimMajorant_nonneg _)
    have hP : 0 ≤ (2 * π * τ) ^ (-(3 : ℝ) / 2) := by positivity
    have hM1 : 0 ≤ gaussianOneDimMajorant (6 * τ)⁻¹ (k 1) :=
      gaussianOneDimMajorant_nonneg _
    have houter0 : 0 ≤ (2 * π * τ) ^ (-(3 : ℝ) / 2) *
        (B * gaussianOneDimMajorant ((6 * τ)⁻¹ / 2) (k 0)) *
          gaussianOneDimMajorant (6 * τ)⁻¹ (k 1) :=
      mul_nonneg (mul_nonneg hP hBmul0) hM1
    rw [gaussKernel_eq_prod]
    conv_lhs =>
      simp only [Fin.prod_univ_three, Pi.add_apply]
    calc
      (4 * π * s) ^ (-(3 : ℝ) / 2) *
          (exp (-(4 * s)⁻¹ * (y 0 + (k 0 : ℝ)) ^ 2) *
            exp (-(4 * s)⁻¹ * (y 1 + (k 1 : ℝ)) ^ 2) *
              exp (-(4 * s)⁻¹ * (y 2 + (k 2 : ℝ)) ^ 2)) *
          (y 0 + (k 0 : ℝ)) ^ 2 =
        (4 * π * s) ^ (-(3 : ℝ) / 2) *
          ((y 0 + (k 0 : ℝ)) ^ 2 *
            exp (-(4 * s)⁻¹ * (y 0 + (k 0 : ℝ)) ^ 2)) *
          exp (-(4 * s)⁻¹ * (y 1 + (k 1 : ℝ)) ^ 2) *
            exp (-(4 * s)⁻¹ * (y 2 + (k 2 : ℝ)) ^ 2) := by ring
      _ ≤ (2 * π * τ) ^ (-(3 : ℝ) / 2) *
          (B * gaussianOneDimMajorant ((6 * τ)⁻¹ / 2) (k 0)) *
          gaussianOneDimMajorant (6 * τ)⁻¹ (k 1) *
            gaussianOneDimMajorant (6 * τ)⁻¹ (k 2) := by
        gcongr
      _ = (2 * π * τ) ^ (-(3 : ℝ) / 2) *
          ∏ j, gaussianTimeDerivativeFactor τ B 0 j (k j) := by
        unfold gaussianTimeDerivativeFactor
        simp [Fin.prod_univ_three]
        ring
  · have h0 := gaussian_exp_interval_bound hτ hs (hy 0) (k 0)
    have hpoly := gaussian_sq_exp_interval_bound hτ hs hB (hy 1) (k 1)
    have h2 := gaussian_exp_interval_bound hτ hs (hy 2) (k 2)
    have hBmul1 : 0 ≤ B * gaussianOneDimMajorant ((6 * τ)⁻¹ / 2) (k 1) :=
      mul_nonneg hB0 (gaussianOneDimMajorant_nonneg _)
    have hP : 0 ≤ (2 * π * τ) ^ (-(3 : ℝ) / 2) := by positivity
    have hM0 : 0 ≤ gaussianOneDimMajorant (6 * τ)⁻¹ (k 0) :=
      gaussianOneDimMajorant_nonneg _
    have hPmulM0 : 0 ≤ (2 * π * τ) ^ (-(3 : ℝ) / 2) *
        gaussianOneDimMajorant (6 * τ)⁻¹ (k 0) :=
      mul_nonneg hP hM0
    have houter1 : 0 ≤ (2 * π * τ) ^ (-(3 : ℝ) / 2) *
        gaussianOneDimMajorant (6 * τ)⁻¹ (k 0) *
          (B * gaussianOneDimMajorant ((6 * τ)⁻¹ / 2) (k 1)) :=
      mul_nonneg hPmulM0 hBmul1
    rw [gaussKernel_eq_prod]
    conv_lhs =>
      simp only [Fin.prod_univ_three, Pi.add_apply]
    calc
      (4 * π * s) ^ (-(3 : ℝ) / 2) *
          (exp (-(4 * s)⁻¹ * (y 0 + (k 0 : ℝ)) ^ 2) *
            exp (-(4 * s)⁻¹ * (y 1 + (k 1 : ℝ)) ^ 2) *
              exp (-(4 * s)⁻¹ * (y 2 + (k 2 : ℝ)) ^ 2)) *
          (y 1 + (k 1 : ℝ)) ^ 2 =
        (4 * π * s) ^ (-(3 : ℝ) / 2) *
          exp (-(4 * s)⁻¹ * (y 0 + (k 0 : ℝ)) ^ 2) *
          ((y 1 + (k 1 : ℝ)) ^ 2 *
            exp (-(4 * s)⁻¹ * (y 1 + (k 1 : ℝ)) ^ 2)) *
          exp (-(4 * s)⁻¹ * (y 2 + (k 2 : ℝ)) ^ 2) := by ring
      _ ≤ (2 * π * τ) ^ (-(3 : ℝ) / 2) *
          gaussianOneDimMajorant (6 * τ)⁻¹ (k 0) *
          (B * gaussianOneDimMajorant ((6 * τ)⁻¹ / 2) (k 1)) *
          gaussianOneDimMajorant (6 * τ)⁻¹ (k 2) := by
        gcongr
      _ = (2 * π * τ) ^ (-(3 : ℝ) / 2) *
          ∏ j, gaussianTimeDerivativeFactor τ B 1 j (k j) := by
        unfold gaussianTimeDerivativeFactor
        simp [Fin.prod_univ_three]
        ring
  · have h0 := gaussian_exp_interval_bound hτ hs (hy 0) (k 0)
    have h1 := gaussian_exp_interval_bound hτ hs (hy 1) (k 1)
    have hpoly := gaussian_sq_exp_interval_bound hτ hs hB (hy 2) (k 2)
    have hBmul2 : 0 ≤ B * gaussianOneDimMajorant ((6 * τ)⁻¹ / 2) (k 2) :=
      mul_nonneg hB0 (gaussianOneDimMajorant_nonneg _)
    have hP : 0 ≤ (2 * π * τ) ^ (-(3 : ℝ) / 2) := by positivity
    have hM0 : 0 ≤ gaussianOneDimMajorant (6 * τ)⁻¹ (k 0) :=
      gaussianOneDimMajorant_nonneg _
    have hM1 : 0 ≤ gaussianOneDimMajorant (6 * τ)⁻¹ (k 1) :=
      gaussianOneDimMajorant_nonneg _
    have hPmulM0 : 0 ≤ (2 * π * τ) ^ (-(3 : ℝ) / 2) *
        gaussianOneDimMajorant (6 * τ)⁻¹ (k 0) :=
      mul_nonneg hP hM0
    have houter2 : 0 ≤ (2 * π * τ) ^ (-(3 : ℝ) / 2) *
        gaussianOneDimMajorant (6 * τ)⁻¹ (k 0) *
          gaussianOneDimMajorant (6 * τ)⁻¹ (k 1) :=
      mul_nonneg hPmulM0 hM1
    rw [gaussKernel_eq_prod]
    conv_lhs =>
      simp only [Fin.prod_univ_three, Pi.add_apply]
    calc
      (4 * π * s) ^ (-(3 : ℝ) / 2) *
          (exp (-(4 * s)⁻¹ * (y 0 + (k 0 : ℝ)) ^ 2) *
            exp (-(4 * s)⁻¹ * (y 1 + (k 1 : ℝ)) ^ 2) *
              exp (-(4 * s)⁻¹ * (y 2 + (k 2 : ℝ)) ^ 2)) *
          (y 2 + (k 2 : ℝ)) ^ 2 =
        (4 * π * s) ^ (-(3 : ℝ) / 2) *
          exp (-(4 * s)⁻¹ * (y 0 + (k 0 : ℝ)) ^ 2) *
          exp (-(4 * s)⁻¹ * (y 1 + (k 1 : ℝ)) ^ 2) *
          ((y 2 + (k 2 : ℝ)) ^ 2 *
            exp (-(4 * s)⁻¹ * (y 2 + (k 2 : ℝ)) ^ 2)) := by ring
      _ ≤ (2 * π * τ) ^ (-(3 : ℝ) / 2) *
          gaussianOneDimMajorant (6 * τ)⁻¹ (k 0) *
          gaussianOneDimMajorant (6 * τ)⁻¹ (k 1) *
          (B * gaussianOneDimMajorant ((6 * τ)⁻¹ / 2) (k 2) ) := by
        gcongr
      _ = (2 * π * τ) ^ (-(3 : ℝ) / 2) *
          ∏ j, gaussianTimeDerivativeFactor τ B 2 j (k j) := by
        unfold gaussianTimeDerivativeFactor
        simp [Fin.prod_univ_three]
        ring

theorem gaussKernel_interval_bound {τ s : ℝ} (hτ : 0 < τ)
    (hs : s ∈ Icc (τ / 2) (3 * τ / 2)) (y : Fin 3 → ℝ)
    (hy : ∀ j, y j ∈ Icc (-1 / 2 : ℝ) (1 / 2)) (k : Fin 3 → ℤ) :
    gaussKernel s (y + fun j => (k j : ℝ)) ≤
      (2 * π * τ) ^ (-(3 : ℝ) / 2) *
        ∏ j, gaussianOneDimMajorant (6 * τ)⁻¹ (k j) := by
  have hbounds := gaussian_time_interval_bounds hτ hs
  have hpref : (4 * π * s) ^ (-(3 : ℝ) / 2) ≤
      (2 * π * τ) ^ (-(3 : ℝ) / 2) := hbounds.2.2.2
  have h0 := gaussian_exp_interval_bound hτ hs (hy 0) (k 0)
  have h1 := gaussian_exp_interval_bound hτ hs (hy 1) (k 1)
  have h2 := gaussian_exp_interval_bound hτ hs (hy 2) (k 2)
  have hspos : 0 < s := hbounds.1
  have hbase : 0 ≤ 4 * π * s := by positivity
  have hpref_s : 0 ≤ (4 * π * s) ^ (-(3 : ℝ) / 2) :=
    Real.rpow_nonneg hbase _
  have hM0 : 0 ≤ gaussianOneDimMajorant (6 * τ)⁻¹ (k 0) :=
    gaussianOneDimMajorant_nonneg _
  have hM1 : 0 ≤ gaussianOneDimMajorant (6 * τ)⁻¹ (k 1) :=
    gaussianOneDimMajorant_nonneg _
  have hM2 : 0 ≤ gaussianOneDimMajorant (6 * τ)⁻¹ (k 2) :=
    gaussianOneDimMajorant_nonneg _
  rw [gaussKernel_eq_prod]
  conv_lhs =>
    simp only [Fin.prod_univ_three, Pi.add_apply]
  calc
    (4 * π * s) ^ (-(3 : ℝ) / 2) *
        (exp (-(4 * s)⁻¹ * (y 0 + (k 0 : ℝ)) ^ 2) *
          exp (-(4 * s)⁻¹ * (y 1 + (k 1 : ℝ)) ^ 2) *
            exp (-(4 * s)⁻¹ * (y 2 + (k 2 : ℝ)) ^ 2) ) ≤
        (4 * π * s) ^ (-(3 : ℝ) / 2) *
          (gaussianOneDimMajorant (6 * τ)⁻¹ (k 0) *
            exp (-(4 * s)⁻¹ * (y 1 + (k 1 : ℝ)) ^ 2) *
              exp (-(4 * s)⁻¹ * (y 2 + (k 2 : ℝ)) ^ 2)) := by
      gcongr
  _ ≤ (4 * π * s) ^ (-(3 : ℝ) / 2) *
        (gaussianOneDimMajorant (6 * τ)⁻¹ (k 0) *
          gaussianOneDimMajorant (6 * τ)⁻¹ (k 1) *
            exp (-(4 * s)⁻¹ * (y 2 + (k 2 : ℝ)) ^ 2)) := by
    gcongr
  _ ≤ (4 * π * s) ^ (-(3 : ℝ) / 2) *
        (gaussianOneDimMajorant (6 * τ)⁻¹ (k 0) *
          gaussianOneDimMajorant (6 * τ)⁻¹ (k 1) *
            gaussianOneDimMajorant (6 * τ)⁻¹ (k 2)) := by
    gcongr
  _ ≤ (2 * π * τ) ^ (-(3 : ℝ) / 2) *
        (gaussianOneDimMajorant (6 * τ)⁻¹ (k 0) *
          gaussianOneDimMajorant (6 * τ)⁻¹ (k 1) *
            gaussianOneDimMajorant (6 * τ)⁻¹ (k 2)) := by
    gcongr
  _ = (2 * π * τ) ^ (-(3 : ℝ) / 2) *
        ∏ j, gaussianOneDimMajorant (6 * τ)⁻¹ (k j) := by
    simp only [Fin.prod_univ_three]

theorem gaussKernel_space_second_interval_bound {τ s B : ℝ} (hτ : 0 < τ)
    (hs : s ∈ Icc (τ / 2) (3 * τ / 2)) (hB0 : 0 ≤ B)
    (hB : ∀ y ∈ Icc (-1 / 2 : ℝ) (1 / 2), ∀ k : ℤ,
      (y + (k : ℝ)) ^ 2 * exp (-(6 * τ)⁻¹ * (y + (k : ℝ)) ^ 2) ≤
        B * gaussianOneDimMajorant ((6 * τ)⁻¹ / 2) k)
    (i : Fin 3) (y : Fin 3 → ℝ) (hy : ∀ j, y j ∈ Icc (-1 / 2 : ℝ) (1 / 2))
    (k : Fin 3 → ℤ) :
    ‖iteratedDeriv 2 (gaussKernelSpaceLine s i y k) (y i)‖ ≤
      gaussianTimeDerivativeMajorant τ B i k := by
  have hbounds := gaussian_time_interval_bounds hτ hs
  have hspos : 0 < s := hbounds.1
  have hc : 0 ≤ (4 * s)⁻¹ := by positivity
  have hC : (4 * s)⁻¹ ≤ (2 * τ)⁻¹ := hbounds.2.2.1
  have hCsq : ((4 * s)⁻¹) ^ 2 ≤ ((2 * τ)⁻¹) ^ 2 := by
    have hC0 : 0 ≤ (2 * τ)⁻¹ := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hC) (add_nonneg hc hC0)]
  have hG0 : 0 ≤ gaussKernel s (y + fun j => (k j : ℝ)) :=
    gaussKernel_nonneg hspos _
  have hG := gaussKernel_interval_bound hτ hs y hy k
  have hGu := gaussKernel_sq_factor_interval_bound hτ hs hB0 hB i y hy k
  have hfactor_nonneg : ∀ j, 0 ≤ gaussianTimeDerivativeFactor τ B i j (k j) := by
    intro j
    by_cases hji : j = i
    · rw [gaussianTimeDerivativeFactor, ite_eq_left hji]
      exact mul_nonneg hB0 (gaussianOneDimMajorant_nonneg _)
    · rw [gaussianTimeDerivativeFactor, ite_eq_right hji]
      exact gaussianOneDimMajorant_nonneg _
  have hfactorprod : 0 ≤ ∏ j, gaussianTimeDerivativeFactor τ B i j (k j) := by
    exact Finset.prod_nonneg (fun j _ => hfactor_nonneg j)
  have hMprod : 0 ≤ ∏ j, gaussianOneDimMajorant (6 * τ)⁻¹ (k j) := by
    exact Finset.prod_nonneg (fun j _ => gaussianOneDimMajorant_nonneg _)
  have hP : 0 ≤ (2 * π * τ) ^ (-(3 : ℝ) / 2) := by positivity
  have hfirst : 4 * (4 * s)⁻¹ ^ 2 *
      (gaussKernel s (y + fun j => (k j : ℝ)) * (y i + (k i : ℝ)) ^ 2) ≤
      4 * (2 * τ)⁻¹ ^ 2 *
        ((2 * π * τ) ^ (-(3 : ℝ) / 2) *
          ∏ j, gaussianTimeDerivativeFactor τ B i j (k j)) := by
    calc
      4 * (4 * s)⁻¹ ^ 2 *
          (gaussKernel s (y + fun j => (k j : ℝ)) * (y i + (k i : ℝ)) ^ 2) ≤
          4 * (2 * τ)⁻¹ ^ 2 *
            (gaussKernel s (y + fun j => (k j : ℝ)) *
              (y i + (k i : ℝ)) ^ 2) := by
        gcongr
      _ ≤ 4 * (2 * τ)⁻¹ ^ 2 *
          ((2 * π * τ) ^ (-(3 : ℝ) / 2) *
            ∏ j, gaussianTimeDerivativeFactor τ B i j (k j)) := by
        gcongr
  have hsecond : 2 * (4 * s)⁻¹ * gaussKernel s (y + fun j => (k j : ℝ)) ≤
      2 * (2 * τ)⁻¹ *
        ((2 * π * τ) ^ (-(3 : ℝ) / 2) *
          ∏ j, gaussianOneDimMajorant (6 * τ)⁻¹ (k j)) := by
    calc
      2 * (4 * s)⁻¹ * gaussKernel s (y + fun j => (k j : ℝ)) ≤
          2 * (2 * τ)⁻¹ * gaussKernel s (y + fun j => (k j : ℝ)) := by
        gcongr
      _ ≤ 2 * (2 * τ)⁻¹ *
          ((2 * π * τ) ^ (-(3 : ℝ) / 2) *
            ∏ j, gaussianOneDimMajorant (6 * τ)⁻¹ (k j)) := by
        gcongr
  rw [gaussKernel_space_second_eq_lattice]
  rw [norm_mul, Real.norm_of_nonneg hG0]
  have hA : 0 ≤ 4 * (4 * s)⁻¹ ^ 2 * (y i + (k i : ℝ)) ^ 2 := by
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  have hB' : 0 ≤ 2 * (4 * s)⁻¹ := mul_nonneg (by norm_num) hc
  have habs : |4 * (4 * s)⁻¹ ^ 2 * (y i + (k i : ℝ)) ^ 2 -
      2 * (4 * s)⁻¹| ≤
      4 * (4 * s)⁻¹ ^ 2 * (y i + (k i : ℝ)) ^ 2 + 2 * (4 * s)⁻¹ := by
    calc
      |4 * (4 * s)⁻¹ ^ 2 * (y i + (k i : ℝ)) ^ 2 - 2 * (4 * s)⁻¹| ≤
          |4 * (4 * s)⁻¹ ^ 2 * (y i + (k i : ℝ)) ^ 2| +
            |2 * (4 * s)⁻¹| := by
        simpa only [sub_zero, zero_sub, abs_neg] using (abs_sub_le
          (4 * (4 * s)⁻¹ ^ 2 * (y i + (k i : ℝ)) ^ 2) 0 (2 * (4 * s)⁻¹))
      _ = 4 * (4 * s)⁻¹ ^ 2 * (y i + (k i : ℝ)) ^ 2 + 2 * (4 * s)⁻¹ := by
        rw [abs_of_nonneg hA, abs_of_nonneg hB']
  calc
    gaussKernel s (y + fun j => (k j : ℝ)) *
        |4 * (4 * s)⁻¹ ^ 2 * (y i + (k i : ℝ)) ^ 2 - 2 * (4 * s)⁻¹| ≤
        gaussKernel s (y + fun j => (k j : ℝ)) *
          (4 * (4 * s)⁻¹ ^ 2 * (y i + (k i : ℝ)) ^ 2 + 2 * (4 * s)⁻¹) :=
      mul_le_mul_of_nonneg_left habs hG0
    _ = 4 * (4 * s)⁻¹ ^ 2 *
          (gaussKernel s (y + fun j => (k j : ℝ)) * (y i + (k i : ℝ)) ^ 2) +
        2 * (4 * s)⁻¹ * gaussKernel s (y + fun j => (k j : ℝ)) := by ring
    _ ≤ 4 * (2 * τ)⁻¹ ^ 2 *
          ((2 * π * τ) ^ (-(3 : ℝ) / 2) *
            ∏ j, gaussianTimeDerivativeFactor τ B i j (k j)) +
        2 * (2 * τ)⁻¹ *
          ((2 * π * τ) ^ (-(3 : ℝ) / 2) *
            ∏ j, gaussianOneDimMajorant (6 * τ)⁻¹ (k j)) :=
      add_le_add hfirst hsecond
    _ = gaussianTimeDerivativeMajorant τ B i k := by
      unfold gaussianTimeDerivativeMajorant
      ring

theorem hasDerivAt_heatKernelLift_time {τ : ℝ} (hτ : 0 < τ)
    (y : Fin 3 → ℝ) (hy : ∀ j, y j ∈ Icc (-1 / 2 : ℝ) (1 / 2)) :
    HasDerivAt (fun s => heatKernelLift s y)
      (∑' k : Fin 3 → ℤ, ∑ i : Fin 3,
        iteratedDeriv 2 (gaussKernelSpaceLine τ i y k) (y i)) τ := by
  obtain ⟨B, hB0, hB⟩ := exists_gaussian_sq_exp_lattice_majorant
    (a := (6 * τ)⁻¹) (by positivity)
  have hu : Summable (fun k : Fin 3 → ℤ => ∑ i : Fin 3,
      gaussianTimeDerivativeMajorant τ B i k) := by
    have h0 := summable_gaussianTimeDerivativeMajorant hτ hB0 (0 : Fin 3)
    have h1 := summable_gaussianTimeDerivativeMajorant hτ hB0 (1 : Fin 3)
    have h2 := summable_gaussianTimeDerivativeMajorant hτ hB0 (2 : Fin 3)
    simpa only [Fin.sum_univ_three] using (h0.add h1).add h2
  have hbase : Summable (fun k : Fin 3 → ℤ =>
      gaussKernel τ (y + fun j => (k j : ℝ))) := by
    have hycc : ∀ j, y j ∈ Icc (-1 : ℝ) 2 := by
      intro j
      exact ⟨by linarith [(hy j).1], by linarith [(hy j).2]⟩
    apply Summable.of_norm_bounded (summable_gaussian_vector_majorant hτ)
    intro k
    exact gaussKernel_le_uniform_majorant hτ hycc k
  unfold heatKernelLift
  apply hasDerivAt_tsum_of_isPreconnected (y₀ := τ) (y := τ) hu isOpen_Ioo
    isPreconnected_Ioo
  · intro k s hs
    have ht2 : 0 < τ / 2 := by positivity
    have hspos : 0 < s := ht2.trans hs.1
    have htime := hasDerivAt_gaussKernel_time_explicit hspos
      (y + fun j => (k j : ℝ))
    refine htime.congr_deriv ?_
    calc
      _ = deriv (fun r => gaussKernel r (y + fun j => (k j : ℝ))) s :=
        htime.deriv.symm
      _ = ∑ i : Fin 3, iteratedDeriv 2 (gaussKernelSpaceLine s i y k) (y i) :=
        gaussKernel_lattice_time_deriv_eq_space_second hspos y k
  · intro k s hs
    have hsIcc : s ∈ Icc (τ / 2) (3 * τ / 2) :=
      ⟨le_of_lt hs.1, le_of_lt hs.2⟩
    have h0 := gaussKernel_space_second_interval_bound hτ hsIcc hB0 hB
      (0 : Fin 3) y hy k
    have h1 := gaussKernel_space_second_interval_bound hτ hsIcc hB0 hB
      (1 : Fin 3) y hy k
    have h2 := gaussKernel_space_second_interval_bound hτ hsIcc hB0 hB
      (2 : Fin 3) y hy k
    simp only [Fin.sum_univ_three]
    calc
      ‖iteratedDeriv 2 (gaussKernelSpaceLine s 0 y k) (y 0) +
          iteratedDeriv 2 (gaussKernelSpaceLine s 1 y k) (y 1) +
            iteratedDeriv 2 (gaussKernelSpaceLine s 2 y k) (y 2)‖ ≤
          ‖iteratedDeriv 2 (gaussKernelSpaceLine s 0 y k) (y 0) +
              iteratedDeriv 2 (gaussKernelSpaceLine s 1 y k) (y 1)‖ +
            ‖iteratedDeriv 2 (gaussKernelSpaceLine s 2 y k) (y 2)‖ :=
        norm_add_le _ _
      _ ≤ (‖iteratedDeriv 2 (gaussKernelSpaceLine s 0 y k) (y 0)‖ +
            ‖iteratedDeriv 2 (gaussKernelSpaceLine s 1 y k) (y 1)‖) +
          ‖iteratedDeriv 2 (gaussKernelSpaceLine s 2 y k) (y 2)‖ := by
        exact add_le_add_left
          (norm_add_le (iteratedDeriv 2 (gaussKernelSpaceLine s 0 y k) (y 0))
            (iteratedDeriv 2 (gaussKernelSpaceLine s 1 y k) (y 1))) _
      _ ≤ gaussianTimeDerivativeMajorant τ B 0 k +
          gaussianTimeDerivativeMajorant τ B 1 k +
            gaussianTimeDerivativeMajorant τ B 2 k := by
        exact add_le_add (add_le_add h0 h1) h2
  · constructor <;> linarith [hτ]
  · exact hbase
  · constructor <;> linarith [hτ]

end RegularityStructures

end
