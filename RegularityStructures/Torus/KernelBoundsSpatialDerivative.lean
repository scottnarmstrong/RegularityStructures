/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.KernelBoundsDerivative
public import RegularityStructures.Analysis.Kernel.Schwartz

/-!
# One-dimensional Gaussian derivative bounds

The spatial factors of the Euclidean Gaussian are Schwartz functions.  This module exposes the
uniform bound for each iterated derivative that is used when differentiating a periodised
Gaussian term-by-term.  It is a preparatory component of Hairer's derivative estimate (5.4).
-/

@[expose] public noncomputable section

open Real
open scoped ContDiff

namespace RegularityStructures

theorem iteratedDeriv_ofReal_expPowFun (c : ℝ) (j n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y : ℝ => (expPowFun c (2 * j) y : ℂ)) x =
      ((iteratedDeriv n (fun y : ℝ => expPowFun c (2 * j) y) x : ℝ) : ℂ) := by
  conv_lhs => rw [iteratedDeriv_eq_iteratedFDeriv]
  conv_rhs => rw [iteratedDeriv_eq_iteratedFDeriv]
  have hcont : ContDiff ℝ ∞ (expPowFun c (2 * j)) := by
    unfold expPowFun
    fun_prop
  have hcomp := Complex.ofRealCLM.iteratedFDeriv_comp_left (x := x) (i := n)
    hcont.contDiffAt (by simp)
  have hcomp' := congrArg (fun L => L (fun _ : Fin n => (1 : ℝ))) hcomp
  simpa [Function.comp_def] using hcomp'

theorem exists_bound_iteratedDeriv_expPowFun {c : ℝ} (hc : 0 < c) {j : ℕ} (hj : 0 < j)
    (n : ℕ) :
    ∃ B : ℝ, ∀ x : ℝ, |iteratedDeriv n (expPowFun c (2 * j)) x| ≤ B := by
  let f : SchwartzMap ℝ ℂ := expPowSchwartz hc hj
  have hB : ∀ x : ℝ,
      ‖iteratedFDeriv ℝ n (f : ℝ → ℂ) x‖ ≤ (SchwartzMap.seminorm ℝ 0 n) f :=
    fun x => SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ f n x
  refine ⟨(SchwartzMap.seminorm ℝ 0 n) f, fun x => ?_⟩
  have h := hB x
  change ‖iteratedFDeriv ℝ n
    (fun y : ℝ => (expPowFun c (2 * j) y : ℂ)) x‖ ≤ _ at h
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at h
  have heq : ‖iteratedDeriv n
      (fun y : ℝ => (expPowFun c (2 * j) y : ℂ)) x‖ =
      |iteratedDeriv n (fun y : ℝ => expPowFun c (2 * j) y) x| := by
    have hderiv := iteratedDeriv_ofReal_expPowFun c j n x
    calc
      _ = ‖((iteratedDeriv n (fun y : ℝ => expPowFun c (2 * j) y) x : ℝ) : ℂ)‖ :=
        congrArg norm hderiv
      _ = _ := by rw [Complex.norm_real, Real.norm_eq_abs]
  rw [← heq]
  exact h

theorem exists_bound_abs_pow_mul_iteratedDeriv_expPowFun {c : ℝ} (hc : 0 < c) {j : ℕ}
    (hj : 0 < j) (m n : ℕ) :
    ∃ B : ℝ, ∀ x : ℝ,
      |x| ^ m * |iteratedDeriv n (expPowFun c (2 * j)) x| ≤ B := by
  let f : SchwartzMap ℝ ℂ := expPowSchwartz hc hj
  refine ⟨(SchwartzMap.seminorm ℝ m n) f, fun x => ?_⟩
  have h := SchwartzMap.le_seminorm ℝ m n f x
  change |x| ^ m * ‖iteratedFDeriv ℝ n
    (fun y : ℝ => (expPowFun c (2 * j) y : ℂ)) x‖ ≤ _ at h
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at h
  have heq : ‖iteratedDeriv n
      (fun y : ℝ => (expPowFun c (2 * j) y : ℂ)) x‖ =
      |iteratedDeriv n (fun y : ℝ => expPowFun c (2 * j) y) x| := by
    have hderiv := iteratedDeriv_ofReal_expPowFun c j n x
    calc
      _ = ‖((iteratedDeriv n (fun y : ℝ => expPowFun c (2 * j) y) x : ℝ) : ℂ)‖ :=
        congrArg norm hderiv
      _ = _ := by rw [Complex.norm_real, Real.norm_eq_abs]
  rw [heq] at h
  exact h

end RegularityStructures

end
