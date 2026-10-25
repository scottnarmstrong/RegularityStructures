/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Polynomial moments of a one-dimensional Gaussian

The Gaussian Poincare proof uses polynomial growth only as an explicit analytic hypothesis.
This file records the corresponding moment closure, using Fernique's finite-moment theorem.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace RegularityStructures

theorem memLp_polynomially_bounded_gaussian {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (gaussianReal 0 1))
    (hgrowth : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ x : ℝ, |f x| ≤ C * (1 + ‖x‖) ^ N)
    (p : ℝ≥0∞) (hp_top : p ≠ ∞) :
    MemLp f p (gaussianReal 0 1) := by
  rcases hgrowth with ⟨C, N, hC, hbound⟩
  by_cases hN : N = 0
  · subst N
    have hconst : MemLp (fun _ : ℝ => C) p (gaussianReal 0 1) := memLp_const C
    apply hconst.mono' hf
    filter_upwards [] with x
    simpa [Real.norm_eq_abs] using hbound x
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  let q : ℝ≥0∞ := (N : ℝ≥0∞)
  have hq0 : q ≠ 0 := by
    simp [q, hN]
  have hqtop : q ≠ ∞ := by simp [q]
  have hpq_top : p * q ≠ ∞ := ENNReal.mul_ne_top hp_top hqtop
  have hid : MemLp id (p * q) (gaussianReal 0 1) :=
    IsGaussian.memLp_id (gaussianReal 0 1) (p * q) hpq_top
  have hbase : MemLp (fun x : ℝ => 1 + ‖x‖) (p * q) (gaussianReal 0 1) := by
    have hnorm : MemLp (fun x : ℝ => ‖id x‖) (p * q) (gaussianReal 0 1) := by
      simpa using hid.norm
    convert (memLp_const (1 : ℝ)).add hnorm using 1
    funext x
    simp [id]
  have hpow := hbase.norm_rpow_div q
  have hpq : p * q / q = p := by
    rw [ENNReal.mul_div_cancel_right hq0 hqtop]
  rw [hpq] at hpow
  have hdom := hpow.const_mul C
  apply hdom.mono' hf
  filter_upwards [] with x
  have hx : 0 ≤ 1 + ‖x‖ := by positivity
  have hx' : 0 < 1 + |x| := by positivity
  simpa [q, Real.norm_eq_abs, abs_of_nonneg hx, abs_of_pos hx', Real.rpow_natCast, hC,
    abs_of_nonneg hC] using hbound x

theorem integrable_polynomially_bounded_gaussian {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (gaussianReal 0 1))
    (hgrowth : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ x : ℝ, |f x| ≤ C * (1 + ‖x‖) ^ N) :
    Integrable f (gaussianReal 0 1) := by
  exact memLp_one_iff_integrable.1
    (memLp_polynomially_bounded_gaussian hf hgrowth 1 (by norm_num))

theorem integrable_gaussian_weight_of_integrable {f : ℝ → ℝ}
    (hf : Integrable f (gaussianReal 0 1)) :
    Integrable (fun x => f x * gaussianPDFReal 0 1 x) (volume : Measure ℝ) := by
  have hv : (1 : NNReal) ≠ 0 := one_ne_zero
  rw [gaussianReal_of_var_ne_zero (0 : ℝ) hv] at hf
  rw [integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (ae_of_all _ (fun _ => gaussianPDF_lt_top))] at hf
  refine hf.congr ?_
  filter_upwards [] with x
  simp [smul_eq_mul, mul_comm]

end RegularityStructures

end
