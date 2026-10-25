/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.Basic
public import RegularityStructures.Analysis.Parabolic.ScaledTest
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import RegularityStructures.Abstract.Singular.Window.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Derivatives of `exp (c t)` on parabolic space

`‖D^k (v ↦ exp (c v₀))‖ ≤ |c|^k exp (c v₀)` (`norm_iteratedFDeriv_expTime_le`), and on the closed
unit parabolic ball the derivatives of `1 - exp (c v₀)`, `0 ≤ c ≤ 1`, are bounded by `3 c`
(`norm_iteratedFDeriv_one_sub_expTime_le`).  Used for the factor `(1 - e^{-t})` of the shells of
`K - G^m`.
-/

open scoped ContDiff

public section

open Set

namespace RegularityStructures.Potential

theorem contDiff_expTime (c : ℝ) : ContDiff ℝ ∞ fun v : ParabolicSpace => Real.exp (c * v.1) :=
  Real.contDiff_exp.comp (contDiff_const.mul contDiff_fst)

theorem norm_iteratedFDeriv_expTime_le (c : ℝ) (k : ℕ) (v : ParabolicSpace) :
    ‖iteratedFDeriv ℝ k (fun v : ParabolicSpace => Real.exp (c * v.1)) v‖ ≤
      |c| ^ k * Real.exp (c * v.1) := by
  have e : (fun v : ParabolicSpace => Real.exp (c * v.1)) =
      (fun a : ℝ => Real.exp (c * a)) ∘ (ContinuousLinearMap.fst ℝ ℝ (Fin 3 → ℝ)) := rfl
  have hf : ContDiff ℝ ∞ (fun a : ℝ => Real.exp (c * a)) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right (n := k) (ContinuousLinearMap.fst ℝ ℝ (Fin 3 → ℝ))
    (hf.of_le (by exact_mod_cast le_top)) v (by exact_mod_cast le_refl k)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hL : ‖ContinuousLinearMap.fst ℝ ℝ (Fin 3 → ℝ)‖ ≤ 1 := ContinuousLinearMap.norm_fst_le _ _ _
  have hp : ∏ _i : Fin k, ‖ContinuousLinearMap.fst ℝ ℝ (Fin 3 → ℝ)‖ ≤ 1 := by
    rw [Finset.prod_const]; exact pow_le_one₀ (norm_nonneg _) hL
  have h1 : ‖iteratedFDeriv ℝ k (fun a : ℝ => Real.exp (c * a)) ((ContinuousLinearMap.fst ℝ ℝ
      (Fin 3 → ℝ)) v)‖ = |c| ^ k * Real.exp (c * v.1) := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_exp_const_mul]
    simp [abs_of_pos (Real.exp_pos _)]
  calc _ ≤ ‖iteratedFDeriv ℝ k (fun a : ℝ => Real.exp (c * a)) ((ContinuousLinearMap.fst ℝ ℝ
      (Fin 3 → ℝ)) v)‖ * 1 := by gcongr
    _ = _ := by rw [mul_one, h1]

theorem norm_iteratedFDeriv_one_sub_expTime_le {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (k : ℕ)
    {v : ParabolicSpace} (hv : parabolicNorm v ≤ 1) :
    ‖iteratedFDeriv ℝ k (fun v : ParabolicSpace => 1 - Real.exp (c * v.1)) v‖ ≤ 3 * c := by
  have hv1 : |v.1| ≤ 1 := by
    have := abs_time_sub_le_of_parabolicNorm_le (w := v) (r := 1) hv
    simpa using this
  have hcv : |c * v.1| ≤ c := by
    rw [abs_mul, abs_of_nonneg hc0]
    exact mul_le_of_le_one_right hc0 hv1
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_sub_comm]
    have := Real.abs_exp_sub_one_le (x := c * v.1) (hcv.trans hc1)
    linarith
  · have hE := contDiff_expTime c
    have e : (fun v : ParabolicSpace => 1 - Real.exp (c * v.1)) =
        (fun _ : ParabolicSpace => (1 : ℝ)) - fun v : ParabolicSpace => Real.exp (c * v.1) := rfl
    have h1 := congrFun (iteratedFDeriv_sub (𝕜 := ℝ) (i := k)
      (contDiff_const (c := (1 : ℝ))) (hE.of_le (by exact_mod_cast le_top))) v
    rw [e, h1, iteratedFDeriv_const_of_ne hk.ne']
    simp only [Pi.zero_apply, Pi.sub_apply, zero_sub, norm_neg]
    refine (norm_iteratedFDeriv_expTime_le c k v).trans ?_
    have h2 : c ^ k ≤ c := pow_le_of_le_one hc0 hc1 hk.ne'
    have h3 : Real.exp (c * v.1) ≤ 3 := by
      have : c * v.1 ≤ 1 := (le_abs_self _).trans (hcv.trans hc1)
      calc Real.exp (c * v.1) ≤ Real.exp 1 := Real.exp_le_exp.2 this
        _ ≤ 3 := by have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
    rw [abs_of_nonneg hc0]
    calc c ^ k * Real.exp (c * v.1) ≤ c * 3 :=
          mul_le_mul h2 h3 (Real.exp_pos _).le hc0
      _ = _ := by ring

end RegularityStructures.Potential

end
