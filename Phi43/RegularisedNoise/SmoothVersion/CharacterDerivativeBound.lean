/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Complex.OperatorNorm
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Derivative bounds for Fourier characters

The finite-window characters are exponentials of real linear phases.  This file records the
uniform derivative estimate for the exponential and its composition with a continuous linear map.
The estimate is deliberately independent of the particular phase used in the Fourier
series construction.
-/

@[expose] public section

open Complex
open scoped ContDiff

namespace RegularityStructures.Phi43

private theorem norm_iteratedFDeriv_id_le_one (n : ℕ) (x : ℝ) (hn : 1 ≤ n) :
    ‖iteratedFDeriv ℝ n (fun y : ℝ => y) x‖ ≤ 1 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  change |iteratedDeriv n id x| ≤ 1
  rw [iteratedDeriv_id]
  have hn0 : n ≠ 0 := by omega
  by_cases hn1 : n = 1
  · simp [hn1]
  · simp [hn0, hn1]

theorem norm_iteratedFDeriv_exp_mul_I_le_two (n : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ n (fun y : ℝ => Complex.exp (y * Complex.I)) x‖ ≤ 2 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  rw [show (fun y : ℝ => Complex.exp (y * Complex.I)) =
      (fun y : ℝ => (Real.cos y : ℂ) + (Real.sin y : ℂ) * Complex.I) by
    funext y
    simp [Complex.exp_mul_I]]
  have hcos : ContDiffAt ℝ (n : ℕ∞ω) (fun y : ℝ => (Real.cos y : ℂ)) x := by
    simpa [Function.comp_def] using
      (ContDiff.comp_contDiffAt x Complex.ofRealCLM.contDiff Real.contDiff_cos.contDiffAt)
  have hsin : ContDiffAt ℝ (n : ℕ∞ω) (fun y : ℝ => (Real.sin y : ℂ)) x := by
    simpa [Function.comp_def] using
      (ContDiff.comp_contDiffAt x Complex.ofRealCLM.contDiff Real.contDiff_sin.contDiffAt)
  have hadd : (fun y : ℝ => (Real.cos y : ℂ) + (Real.sin y : ℂ) * Complex.I) =
      (fun y : ℝ => (Real.cos y : ℂ)) +
        (fun y : ℝ => (Real.sin y : ℂ) * Complex.I) := by
    funext y
    rfl
  rw [hadd]
  rw [iteratedDeriv_add hcos (by simpa [smul_eq_mul] using hsin.smul_const Complex.I)]
  rw [iteratedDeriv_mul_const_field (fun y : ℝ => (Real.sin y : ℂ)) Complex.I]
  have hcos' : ‖iteratedDeriv n (fun y : ℝ => (Real.cos y : ℂ)) x‖ ≤ 1 := by
    have hcosReal : ContDiffAt ℝ (n : ℕ∞ω) Real.cos x :=
      (Real.contDiff_cos (n := (n : ℕ∞ω))).contDiffAt
    have h := Complex.ofRealCLM.norm_iteratedFDeriv_comp_left
      hcosReal (x := x) le_rfl
    calc
      ‖iteratedDeriv n (fun y : ℝ => (Real.cos y : ℂ)) x‖ ≤
          |iteratedDeriv n Real.cos x| := by
        simpa [Function.comp_def, norm_iteratedFDeriv_eq_norm_iteratedDeriv] using h
      _ ≤ 1 := Real.abs_iteratedDeriv_cos_le_one n x
  have hsin' : ‖iteratedDeriv n (fun y : ℝ => (Real.sin y : ℂ)) x‖ ≤ 1 := by
    have hsinReal : ContDiffAt ℝ (n : ℕ∞ω) Real.sin x :=
      (Real.contDiff_sin (n := (n : ℕ∞ω))).contDiffAt
    have h := Complex.ofRealCLM.norm_iteratedFDeriv_comp_left
      hsinReal (x := x) le_rfl
    calc
      ‖iteratedDeriv n (fun y : ℝ => (Real.sin y : ℂ)) x‖ ≤
          |iteratedDeriv n Real.sin x| := by
        simpa [Function.comp_def, norm_iteratedFDeriv_eq_norm_iteratedDeriv] using h
      _ ≤ 1 := Real.abs_iteratedDeriv_sin_le_one n x
  calc
    ‖iteratedDeriv n (fun y : ℝ => (Real.cos y : ℂ)) x +
        iteratedDeriv n (fun y : ℝ => (Real.sin y : ℂ)) x * Complex.I‖ ≤
        ‖iteratedDeriv n (fun y : ℝ => (Real.cos y : ℂ)) x‖ +
          ‖iteratedDeriv n (fun y : ℝ => (Real.sin y : ℂ)) x * Complex.I‖ :=
      norm_add_le _ _
    _ ≤ 1 + 1 := by
      rw [norm_mul, Complex.norm_I]
      linarith
    _ = 2 := by norm_num

theorem norm_iteratedFDeriv_exp_mul_I_comp_linear_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] ℝ) (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => Complex.exp (A y * Complex.I)) x‖ ≤
      n.factorial * 2 * ‖A‖ ^ n := by
  let g : ℝ → ℂ := fun y => Complex.exp (y * Complex.I)
  let f : E → ℝ := fun y => A y
  have hg : ContDiff ℝ (⊤ : ℕ∞ω) g := by
    have harg : ContDiff ℝ (⊤ : ℕ∞ω)
        (fun y : ℝ => (y : ℂ) * Complex.I) := by
      exact (Complex.ofRealCLM.contDiff.comp contDiff_id).mul contDiff_const
    simpa [g, Function.comp_def] using Complex.contDiff_exp.comp harg
  have hf : ContDiff ℝ (⊤ : ℕ∞ω) f := A.contDiff
  have hcomp := norm_iteratedFDeriv_comp_le (n := n) (N := (⊤ : ℕ∞ω))
    (g := g) (f := f) hg hf
    (by exact_mod_cast le_top) x
    (C := 2) (D := ‖A‖)
    (fun i hi => by
      simpa [g, f] using norm_iteratedFDeriv_exp_mul_I_le_two i (A x))
    (fun i hi hni => by
      change ‖iteratedFDeriv ℝ i (id ∘ A) x‖ ≤ ‖A‖ ^ i
      rw [A.iteratedFDeriv_comp_right contDiff_id x (by exact_mod_cast le_top)]
      calc
        ‖(iteratedFDeriv ℝ i (fun y : ℝ => y) (A x)).compContinuousLinearMap
            (fun _ : Fin i => A)‖ ≤
            ‖iteratedFDeriv ℝ i (fun y : ℝ => y) (A x)‖ *
              ∏ _ : Fin i, ‖A‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
        _ ≤ (1 : ℝ) * ‖A‖ ^ i := by
          gcongr
          · exact norm_iteratedFDeriv_id_le_one i (A x) hi
          · simp
        _ = ‖A‖ ^ i := by simp
      )
  convert hcomp using 1
  simp [g, f, Function.comp_def]

end RegularityStructures.Phi43

end
