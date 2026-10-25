/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.TaylorGen
public import Mathlib.Analysis.Calculus.TaylorIntegral

/-!
# One-dimensional Taylor remainder along a coordinate direction

`tayOp e s m φ = ∑_{p ≤ m} s^p/p! ∂_e^p φ` and `remOp e s m φ = φ(· + s e) - tayOp e s m φ`.
By Taylor's formula with integral remainder
`remOp e s m φ (w) = (m!)⁻¹ ∫_0^1 (1-t)^m s^{m+1} (∂_e^{m+1} φ)(w + t s e) dt`
(`remOp_eq_integral`), and so `∫ |remOp e s m φ| ≤ |s|^{m+1} ∫ |∂_e^{m+1} φ|`
(`integral_abs_remOp_le`) for `φ` smooth with compact support.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The Taylor polynomial of order `m` in the direction `e` with step `s`. -/
def tayOp (e : ParabolicSpace) (s : ℝ) (m : ℕ) (φ : ParabolicSpace → ℝ) (w : ParabolicSpace) : ℝ :=
  ∑ p ∈ Finset.range (m + 1), ((Nat.factorial p : ℕ) : ℝ)⁻¹ * s ^ p * (dirDeriv e)^[p] φ w

/-- The Taylor remainder of order `m` in the direction `e` with step `s`. -/
def remOp (e : ParabolicSpace) (s : ℝ) (m : ℕ) (φ : ParabolicSpace → ℝ) (w : ParabolicSpace) : ℝ :=
  φ (w + s • e) - tayOp e s m φ w

end RegularityStructures

end

public section

open MeasureTheory Set
open scoped ContDiff

namespace RegularityStructures

theorem iteratedFDeriv_smul_const_apply {φ : ParabolicSpace → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (e : ParabolicSpace) (s : ℝ) (k : ℕ) (w : ParabolicSpace) :
    iteratedFDeriv ℝ k φ w (fun _ => s • e) = s ^ k * (dirDeriv e)^[k] φ w := by
  have := (iteratedFDeriv ℝ k φ w).map_smul_univ (fun _ : Fin k => s) (fun _ => e)
  rw [this]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [← congrFun (iteratedFDeriv_const_eq_iterate hφ e k) w]

theorem remOp_eq_integral {φ : ParabolicSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) (e : ParabolicSpace)
    (s : ℝ) (m : ℕ) (w : ParabolicSpace) :
    remOp e s m φ w = ((Nat.factorial m : ℕ) : ℝ)⁻¹ * ∫ t in (0 : ℝ)..1,
      (1 - t) ^ m * (s ^ (m + 1) * (dirDeriv e)^[m + 1] φ (w + (t * s) • e)) := by
  have hk : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ContDiffAt ℝ (m + 1 : ℕ) φ (w + t • (s • e)) :=
    fun t _ => (hφ.of_le (by exact_mod_cast le_top)).contDiffAt
  have h := map_add_eq_sum_add_integral_iteratedFDeriv (n := m) (x := w) (y := s • e) hk
  have e1 : ∀ k : ℕ, iteratedFDeriv ℝ k φ w (fun _ => s • e) = s ^ k * (dirDeriv e)^[k] φ w :=
    fun k => iteratedFDeriv_smul_const_apply hφ e s k w
  have e2 : ∀ t : ℝ, iteratedFDeriv ℝ (m + 1) φ (w + t • (s • e)) (fun _ => s • e) =
      s ^ (m + 1) * (dirDeriv e)^[m + 1] φ (w + (t * s) • e) := by
    intro t
    rw [iteratedFDeriv_smul_const_apply hφ e s, mul_smul]
  simp only [e1, e2, smul_eq_mul] at h
  rw [remOp, tayOp, h]
  simp only [mul_assoc]
  ring

theorem abs_remOp_le {φ : ParabolicSpace → ℝ} (hφ : ContDiff ℝ ∞ φ) (e : ParabolicSpace) (s : ℝ)
    (m : ℕ) (w : ParabolicSpace) :
    |remOp e s m φ w| ≤ |s| ^ (m + 1) * ∫ t in (0 : ℝ)..1,
      |(dirDeriv e)^[m + 1] φ (w + (t * s) • e)| := by
  set g := (dirDeriv e)^[m + 1] φ with hg
  have hgc : Continuous g := (contDiff_iterate_dirDeriv hφ e (m + 1)).continuous
  have hcont : Continuous fun t : ℝ => |g (w + (t * s) • e)| := by fun_prop
  have hcont2 : Continuous fun t : ℝ =>
      (1 - t) ^ m * (s ^ (m + 1) * g (w + (t * s) • e)) := by fun_prop
  rw [remOp_eq_integral hφ, abs_mul, abs_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))]
  have h1 : |∫ t in (0 : ℝ)..1, (1 - t) ^ m * (s ^ (m + 1) * g (w + (t * s) • e))| ≤
      ∫ t in (0 : ℝ)..1, |s| ^ (m + 1) * |g (w + (t * s) • e)| := by
    refine (intervalIntegral.abs_integral_le_integral_abs zero_le_one).trans ?_
    refine intervalIntegral.integral_mono_on zero_le_one
      (hcont2.abs.intervalIntegrable _ _) ((hcont.const_mul _).intervalIntegrable _ _) ?_
    intro t ht
    rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg (sub_nonneg.2 ht.2)]
    have : (1 - t) ^ m ≤ 1 := pow_le_one₀ (sub_nonneg.2 ht.2) (by linarith [ht.1])
    calc (1 - t) ^ m * (|s ^ (m + 1)| * |g (w + (t * s) • e)|) ≤
        1 * (|s ^ (m + 1)| * |g (w + (t * s) • e)|) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = _ := by rw [one_mul, abs_pow]
  rw [intervalIntegral.integral_const_mul] at h1
  have hf : ((Nat.factorial m : ℕ) : ℝ)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast Nat.factorial_pos m)
  calc ((Nat.factorial m : ℕ) : ℝ)⁻¹ * |∫ t in (0 : ℝ)..1,
        (1 - t) ^ m * (s ^ (m + 1) * g (w + (t * s) • e))|
      ≤ 1 * (|s| ^ (m + 1) * ∫ t in (0 : ℝ)..1, |g (w + (t * s) • e)|) :=
        mul_le_mul hf h1 (abs_nonneg _) zero_le_one
    _ = _ := one_mul _

end RegularityStructures

end
