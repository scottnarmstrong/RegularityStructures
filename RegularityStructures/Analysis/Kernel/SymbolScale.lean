/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Kernel.Symbol
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Exact scaling and moments of the symbol kernels

For `t > 0`, `k_t(b) = t^{-1/(2j)} k_1(t^{-1/(2j)} b)` (exact scaling), and for `s ≥ 0`
`∫ |k_t(b)| |b|^s db = t^{s/(2j)} ∫ |k_1(b)| |b|^s db < ∞`. These are the 1D inputs for the
moment bounds of the parabolic kernel (`RegularityStructures.Analysis.Kernel.Parabolic`).
-/

public section

open MeasureTheory Real

namespace RegularityStructures

variable {j : ℕ} (hj : 0 < j)

/-- The scale `t^{-1/(2j)}` as a positive number with `λ^{2j} = t⁻¹`. -/
theorem rpow_neg_inv_pow {t : ℝ} (ht : 0 < t) (hj : 0 < j) :
    (t ^ (-(1 / ((2 * j : ℕ) : ℝ)))) ^ (2 * j) = t⁻¹ := by
  have hm : ((2 * j : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le, neg_mul, one_div, inv_mul_cancel₀ hm,
    Real.rpow_neg_one]

include hj in
/-- Exact scaling: `k_t(b) = t^{-1/(2j)} k_1(t^{-1/(2j)} b)`. -/
theorem symKernel_eq_scale {t : ℝ} (ht : 0 < t) (b : ℝ) :
    symKernel j t b =
      t ^ (-(1 / ((2 * j : ℕ) : ℝ))) * symKernel j 1 (t ^ (-(1 / ((2 * j : ℕ) : ℝ))) * b) := by
  set l := t ^ (-(1 / ((2 * j : ℕ) : ℝ))) with hl
  have hlpos : 0 < l := Real.rpow_pos_of_pos ht _
  have hlp : l ^ (2 * j) = t⁻¹ := rpow_neg_inv_pow ht hj
  unfold symKernel
  have h := Measure.integral_comp_mul_left
    (fun ξ => Real.exp (-(t * ξ ^ (2 * j))) * Real.cos (2 * π * ξ * b)) l
  beta_reduce at h
  have h2 : ∀ ξ : ℝ, Real.exp (-(t * (l * ξ) ^ (2 * j))) * Real.cos (2 * π * (l * ξ) * b) =
      Real.exp (-(1 * ξ ^ (2 * j))) * Real.cos (2 * π * ξ * (l * b)) := by
    intro ξ
    have : t * (l * ξ) ^ (2 * j) = 1 * ξ ^ (2 * j) := by
      rw [mul_pow, hlp, ← mul_assoc, mul_inv_cancel₀ ht.ne']
    rw [this]
    congr 2
    ring
  simp_rw [h2] at h
  rw [h, smul_eq_mul, abs_of_pos (inv_pos.2 hlpos), ← mul_assoc, mul_inv_cancel₀ hlpos.ne',
    one_mul]

include hj in
/-- The moment weight `|k_1(b)| |b|^s` is integrable. -/
theorem integrable_abs_symKernel_one_mul_rpow {s : ℝ} (hs : 0 ≤ s) :
    Integrable (fun b => |symKernel j 1 b| * |b| ^ s) := by
  obtain ⟨C, hC⟩ := symKernel_one_decay hj (⌈s⌉₊ + 2)
  have hint : Integrable (fun b : ℝ => C * (1 + ‖b‖) ^ (-(2 : ℝ))) :=
    (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by simp)).const_mul C
  have hC0 : 0 ≤ C := by
    have := (abs_nonneg _).trans (hC 0)
    simpa using this
  refine hint.mono' ?_ (Filter.Eventually.of_forall fun b => ?_)
  · exact ((continuous_symKernel one_pos hj).abs.mul (by fun_prop)).aestronglyMeasurable
  · have h1 : 0 ≤ |symKernel j 1 b| * |b| ^ s :=
      mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (abs_nonneg _) _)
    rw [Real.norm_of_nonneg h1]
    have hb : (1 : ℝ) ≤ 1 + |b| := by linarith [abs_nonneg b]
    have h2 : |b| ^ s ≤ (1 + |b|) ^ s :=
      Real.rpow_le_rpow (abs_nonneg b) (by linarith [abs_nonneg b]) hs
    have h3 : (1 + |b|) ^ (-((⌈s⌉₊ + 2 : ℕ) : ℝ)) * (1 + |b|) ^ s ≤ (1 + |b|) ^ (-(2 : ℝ)) := by
      rw [← Real.rpow_add (by linarith [abs_nonneg b])]
      apply Real.rpow_le_rpow_of_exponent_le hb
      have := Nat.le_ceil s
      push_cast
      linarith
    calc |symKernel j 1 b| * |b| ^ s ≤ (C * (1 + |b|) ^ (-((⌈s⌉₊ + 2 : ℕ) : ℝ))) * (1 + |b|) ^ s := by
          exact mul_le_mul (hC b) h2 (Real.rpow_nonneg (abs_nonneg b) _) ((abs_nonneg _).trans (hC b))
      _ = C * ((1 + |b|) ^ (-((⌈s⌉₊ + 2 : ℕ) : ℝ)) * (1 + |b|) ^ s) := by ring
      _ ≤ C * (1 + |b|) ^ (-(2 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left h3 hC0
      _ = _ := by simp

include hj in
theorem abs_symKernel_mul_rpow_eq {t : ℝ} (ht : 0 < t) (s b : ℝ) :
    |symKernel j t b| * |b| ^ s =
      (t ^ (-(1 / ((2 * j : ℕ) : ℝ)))) ^ (1 - s) *
        (fun v => |symKernel j 1 v| * |v| ^ s) (t ^ (-(1 / ((2 * j : ℕ) : ℝ))) * b) := by
  set l := t ^ (-(1 / ((2 * j : ℕ) : ℝ))) with hl
  have hlpos : 0 < l := Real.rpow_pos_of_pos ht _
  simp only
  rw [symKernel_eq_scale hj ht b, ← hl, abs_mul, abs_of_pos hlpos, abs_mul, abs_of_pos hlpos,
    Real.mul_rpow hlpos.le (abs_nonneg b), Real.rpow_sub hlpos, Real.rpow_one]
  field_simp

include hj in
theorem integrable_abs_symKernel_mul_rpow {t : ℝ} (ht : 0 < t) {s : ℝ} (hs : 0 ≤ s) :
    Integrable (fun b => |symKernel j t b| * |b| ^ s) := by
  have hlpos : 0 < t ^ (-(1 / ((2 * j : ℕ) : ℝ))) := Real.rpow_pos_of_pos ht _
  have := ((integrable_abs_symKernel_one_mul_rpow hj hs).comp_mul_left' hlpos.ne').const_mul
    ((t ^ (-(1 / ((2 * j : ℕ) : ℝ)))) ^ (1 - s))
  refine this.congr (Filter.Eventually.of_forall fun b => ?_)
  exact (abs_symKernel_mul_rpow_eq hj ht s b).symm

include hj in
/-- Scaling of the moments: `∫ |k_t(b)| |b|^s db = t^{s/(2j)} ∫ |k_1(b)| |b|^s db`. -/
theorem integral_abs_symKernel_mul_rpow {t : ℝ} (ht : 0 < t) (s : ℝ) :
    ∫ b, |symKernel j t b| * |b| ^ s =
      t ^ (s / ((2 * j : ℕ) : ℝ)) * ∫ b, |symKernel j 1 b| * |b| ^ s := by
  set l := t ^ (-(1 / ((2 * j : ℕ) : ℝ))) with hl
  have hlpos : 0 < l := Real.rpow_pos_of_pos ht _
  simp_rw [abs_symKernel_mul_rpow_eq hj ht s]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun v => |symKernel j 1 v| * |v| ^ s) l,
    smul_eq_mul, abs_of_pos (inv_pos.2 hlpos), ← mul_assoc]
  congr 1
  rw [← Real.rpow_neg_one, ← Real.rpow_add hlpos, hl, ← Real.rpow_mul ht.le]
  congr 1
  ring

/-- The kernels are measurable in `b` for every `t` (also `t ≤ 0`, where the integral is junk). -/
theorem measurable_symKernel (j : ℕ) (t : ℝ) : Measurable (symKernel j t) := by
  have hf : StronglyMeasurable (Function.uncurry fun (b ξ : ℝ) =>
      Real.exp (-(t * ξ ^ (2 * j))) * Real.cos (2 * π * ξ * b)) :=
    Continuous.stronglyMeasurable (by fun_prop)
  exact (hf.integral_prod_right).measurable

/-- The kernels are even. -/
theorem symKernel_neg (j : ℕ) (t b : ℝ) : symKernel j t (-b) = symKernel j t b := by
  unfold symKernel
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only
  rw [show 2 * π * ξ * -b = -(2 * π * ξ * b) by ring, Real.cos_neg]

end RegularityStructures

end
