/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Kernel.GeneratorIBP
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Bridges between `iteratedFDeriv`, `dirDeriv` and reflection

* `iteratedFDeriv_const_eq_iterate`: `iteratedFDeriv ℝ n f w (fun _ => d) = (D_d^n f) w`;
* `iterate_dirDeriv_comp_sub`: `D_d^n (y ↦ c f(z - y)) = (-1)^n c (D_d^n f)(z - ·)`.
-/

public section

open scoped ContDiff

namespace RegularityStructures

theorem iteratedFDeriv_const_eq_iterate {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f)
    (d : ParabolicSpace) (n : ℕ) :
    (fun w => iteratedFDeriv ℝ n f w (fun _ => d)) = (dirDeriv d)^[n] f := by
  induction n with
  | zero => funext w; simp [iteratedFDeriv_zero_apply]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← ih]
    funext w
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) w :=
      (hf.differentiable_iteratedFDeriv (m := n) (by exact_mod_cast ENat.natCast_lt_top n)) w
    rw [dirDeriv, fderiv_continuousMultilinear_apply_const_apply hd,
      iteratedFDeriv_succ_apply_left]
    rfl

theorem dirDeriv_comp_sub {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f) (d z : ParabolicSpace) :
    dirDeriv d (fun y => f (z - y)) = fun y => -dirDeriv d f (z - y) := by
  funext y
  have h1 : HasFDerivAt (fun y : ParabolicSpace => z - y)
      (-(ContinuousLinearMap.id ℝ ParabolicSpace)) y := (hasFDerivAt_id y).const_sub z
  have h2 := ((hf.differentiable (by simp)) (z - y)).hasFDerivAt.comp y h1
  have h3 : fderiv ℝ (fun y => f (z - y)) y = _ := h2.fderiv
  rw [dirDeriv, h3]
  simp [dirDeriv]

theorem dirDeriv_const_mul {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f) (d : ParabolicSpace)
    (c : ℝ) : dirDeriv d (fun y => c * f y) = fun y => c * dirDeriv d f y := by
  funext y
  rw [dirDeriv, fderiv_const_mul ((hf.differentiable (by simp)) y)]
  simp [dirDeriv]

theorem iterate_dirDeriv_comp_sub (d z : ParabolicSpace) (n : ℕ) :
    ∀ (c : ℝ) {f : ParabolicSpace → ℝ}, ContDiff ℝ ∞ f →
      (dirDeriv d)^[n] (fun y => c * f (z - y)) =
        fun y => c * (-1) ^ n * ((dirDeriv d)^[n] f) (z - y) := by
  induction n with
  | zero => intro c f _; funext y; simp
  | succ n ih =>
    intro c f hf
    have hcomp : ContDiff ℝ ∞ (fun y => f (z - y)) := hf.comp (contDiff_const.sub contDiff_id)
    have h1 : dirDeriv d (fun y => c * f (z - y)) = fun y => (-c) * dirDeriv d f (z - y) := by
      rw [dirDeriv_const_mul hcomp, dirDeriv_comp_sub hf]
      funext y
      ring
    rw [Function.iterate_succ_apply, h1, ih (-c) (contDiff_dirDeriv hf d),
      Function.iterate_succ_apply]
    funext y
    ring

end RegularityStructures

end
