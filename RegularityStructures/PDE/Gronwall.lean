/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Grönwall's inequality in integral form

If `φ` is continuous and `φ(t) ≤ a + b ∫₀ᵗ φ` on `[0, T]` with `b ≥ 0`, then
`φ(t) ≤ a e^{bt}` on `[0, T]`. Mathlib states Grönwall's inequality for differential inequalities;
this is the integral form used for mild solutions.
-/

public section

open MeasureTheory Set Real

namespace RegularityStructures.PDE

/-- **Grönwall's inequality**, integral form. -/
theorem le_mul_exp_of_le_add_integral {φ : ℝ → ℝ} {a b T : ℝ} (hφ : Continuous φ)
    (hb : 0 ≤ b) (h : ∀ t ∈ Icc 0 T, φ t ≤ a + b * ∫ s in (0 : ℝ)..t, φ s) :
    ∀ t ∈ Icc 0 T, φ t ≤ a * exp (b * t) := by
  set Ψ : ℝ → ℝ := fun t => a + b * ∫ s in (0 : ℝ)..t, φ s with hΨ
  set K : ℝ → ℝ := fun t => exp (-(b * t)) * Ψ t with hK
  have hprim : ∀ t, HasDerivAt (fun t => ∫ s in (0 : ℝ)..t, φ s) (φ t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hφ.intervalIntegrable 0 t)
      (hφ.stronglyMeasurableAtFilter _ _) hφ.continuousAt
  have hΨd : ∀ t, HasDerivAt Ψ (b * φ t) t := fun t => (hprim t).const_mul b |>.const_add a
  have hKd : ∀ t, HasDerivAt K (exp (-(b * t)) * (-b) * Ψ t + exp (-(b * t)) * (b * φ t)) t := by
    intro t
    have he : HasDerivAt (fun t => exp (-(b * t))) (exp (-(b * t)) * (-b)) t := by
      have := ((hasDerivAt_id t).const_mul b).neg.exp
      simpa using this
    exact he.mul (hΨd t)
  have hanti : AntitoneOn K (Icc 0 T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
      (fun t _ => (hKd t).continuousAt.continuousWithinAt)
      (fun t _ => (hKd t).differentiableAt.differentiableWithinAt) fun t ht => ?_
    rw [interior_Icc] at ht
    rw [(hKd t).deriv]
    have hle : φ t ≤ Ψ t := h t (Ioo_subset_Icc_self ht)
    have hpos : 0 < exp (-(b * t)) := exp_pos _
    have : exp (-(b * t)) * (-b) * Ψ t + exp (-(b * t)) * (b * φ t)
        = exp (-(b * t)) * (b * (φ t - Ψ t)) := by ring
    rw [this]
    exact mul_nonpos_of_nonneg_of_nonpos hpos.le (mul_nonpos_of_nonneg_of_nonpos hb (by linarith))
  intro t ht
  have hT : (0 : ℝ) ≤ T := ht.1.trans ht.2
  have hK0 : K 0 = a := by simp [hK, hΨ]
  have hKt : K t ≤ a := hK0 ▸ hanti ⟨le_rfl, hT⟩ ht ht.1
  have hΨt : Ψ t ≤ a * exp (b * t) := by
    have hpos : 0 < exp (-(b * t)) := exp_pos _
    have h1 : exp (-(b * t)) * Ψ t ≤ a := hKt
    have h2 : Ψ t = exp (b * t) * (exp (-(b * t)) * Ψ t) := by
      rw [← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul]
    rw [h2, mul_comm a]
    exact mul_le_mul_of_nonneg_left h1 (exp_pos _).le
  exact (h t ht).trans hΨt

/-- Grönwall's inequality with `a = 0`: the function vanishes. -/
theorem le_zero_of_le_integral {φ : ℝ → ℝ} {b T : ℝ} (hφ : Continuous φ) (hb : 0 ≤ b)
    (h : ∀ t ∈ Icc 0 T, φ t ≤ b * ∫ s in (0 : ℝ)..t, φ s) : ∀ t ∈ Icc 0 T, φ t ≤ 0 := by
  intro t ht
  have := le_mul_exp_of_le_add_integral (a := 0) hφ hb (fun t ht => by simpa using h t ht) t ht
  simpa using this

end RegularityStructures.PDE

end
