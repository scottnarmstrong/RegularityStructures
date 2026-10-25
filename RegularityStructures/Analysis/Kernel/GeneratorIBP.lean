/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Kernel.GeneratorPDE
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Integration by parts for iterated directional derivatives on `ℝ⁴`

If `ψ` is smooth with compact support and `u` is smooth, then
`∫ (D_d^n u) ψ = (-1)^n ∫ u (D_d^n ψ)`, where `D_d f = f' d`. No decay of `u` is needed.
-/

public section

open MeasureTheory
open scoped ContDiff

namespace RegularityStructures

theorem contDiff_dirDeriv {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f) (d : ParabolicSpace) :
    ContDiff ℝ ∞ (dirDeriv d f) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem contDiff_iterate_dirDeriv {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f)
    (d : ParabolicSpace) (n : ℕ) : ContDiff ℝ ∞ ((dirDeriv d)^[n] f) := by
  induction n with
  | zero => exact hf
  | succ n ih => rw [Function.iterate_succ_apply']; exact contDiff_dirDeriv ih d

theorem hasCompactSupport_dirDeriv {f : ParabolicSpace → ℝ} (hf : HasCompactSupport f)
    (d : ParabolicSpace) : HasCompactSupport (dirDeriv d f) :=
  HasCompactSupport.fderiv_apply ℝ hf d

theorem hasCompactSupport_iterate_dirDeriv {f : ParabolicSpace → ℝ} (hf : HasCompactSupport f)
    (d : ParabolicSpace) (n : ℕ) : HasCompactSupport ((dirDeriv d)^[n] f) := by
  induction n with
  | zero => exact hf
  | succ n ih => rw [Function.iterate_succ_apply']; exact hasCompactSupport_dirDeriv ih d

theorem integral_dirDeriv_mul {u ψ : ParabolicSpace → ℝ} (d : ParabolicSpace)
    (hu : ContDiff ℝ ∞ u) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    ∫ y, dirDeriv d u y * ψ y = -∫ y, u y * dirDeriv d ψ y := by
  have hu' := contDiff_dirDeriv hu d
  have hψ' := contDiff_dirDeriv hψ d
  have hc' := hasCompactSupport_dirDeriv hc d
  have i1 : Integrable fun y => dirDeriv d u y * ψ y :=
    (hu'.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left
  have i2 : Integrable fun y => u y * dirDeriv d ψ y :=
    (hu.continuous.mul hψ'.continuous).integrable_of_hasCompactSupport hc'.mul_left
  have i3 : Integrable fun y => u y * ψ y :=
    (hu.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left
  rw [Measure.volume_eq_prod] at i1 i2 i3
  have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure ℝ).prod (volume : Measure (Fin 3 → ℝ)))
    (f := u) (g := ψ) (v := d) i1 i2 i3 (fun x _ => (hu.differentiable (by simp)) x)
    (fun x _ => (hψ.differentiable (by simp)) x)
  simp only [dirDeriv]
  rw [Measure.volume_eq_prod, this]
  ring

theorem integral_iterate_dirDeriv_mul (d : ParabolicSpace) (n : ℕ) {u ψ : ParabolicSpace → ℝ}
    (hu : ContDiff ℝ ∞ u) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    ∫ y, ((dirDeriv d)^[n] u) y * ψ y = (-1) ^ n * ∫ y, u y * ((dirDeriv d)^[n] ψ) y := by
  induction n generalizing u with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih (contDiff_dirDeriv hu d), integral_dirDeriv_mul d hu
      (contDiff_iterate_dirDeriv hψ d n) (hasCompactSupport_iterate_dirDeriv hc d n),
      Function.iterate_succ_apply']
    ring

end RegularityStructures

end
