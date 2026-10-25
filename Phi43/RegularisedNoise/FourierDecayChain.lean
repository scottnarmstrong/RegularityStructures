/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Fourier.AddCircle

/-!
# Iterated one-dimensional Fourier decay

The coefficient form of integration by parts is the form that can be iterated along a chain of
periodic derivatives.  It is kept separate from the elementary one-step estimate so that the
multivariate Fourier-decay argument can apply it one coordinate at a time.
-/

@[expose] public section

open MeasureTheory Set

namespace RegularityStructures.Phi43

theorem norm_fourierCoeffOn_le_of_intervalIntegrable
    {a b : ℝ} (hab : a < b) {f : ℝ → ℂ} (n : ℤ) :
    ‖fourierCoeffOn hab f n‖ ≤
      (b - a)⁻¹ * ∫ x in a..b, ‖f x‖ := by
  rw [fourierCoeffOn_eq_integral f n hab]
  calc
    ‖(1 / (b - a) : ℝ) • ∫ x in a..b,
        fourier (-n) (x : AddCircle (b - a)) • f x‖ =
        (b - a)⁻¹ * ‖∫ x in a..b,
          fourier (-n) (x : AddCircle (b - a)) • f x‖ := by
            rw [norm_smul, Real.norm_eq_abs,
              abs_of_pos (one_div_pos.mpr (sub_pos.mpr hab)), one_div]
    _ ≤ (b - a)⁻¹ * ∫ x in a..b, ‖f x‖ := by
      have hnorm : ∀ x : ℝ,
          ‖fourier (-n) (x : AddCircle (b - a)) • f x‖ = ‖f x‖ := by
        intro x
        rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul]
      calc
        (b - a)⁻¹ * ‖∫ x in a..b,
            fourier (-n) (x : AddCircle (b - a)) • f x‖ ≤
            (b - a)⁻¹ * ∫ x in a..b,
              ‖fourier (-n) (x : AddCircle (b - a)) • f x‖ := by
                gcongr
                exact intervalIntegral.norm_integral_le_integral_norm
                  (μ := volume) hab.le
        _ = (b - a)⁻¹ * ∫ x in a..b, ‖f x‖ := by simp_rw [hnorm]

theorem norm_fourierCoeffOn_le_of_hasDerivAt_coeff
    {a b : ℝ} (hab : a < b) {f f' : ℝ → ℂ} {n : ℤ} (hn : n ≠ 0)
    (hf : ∀ x, x ∈ Icc a b → HasDerivAt f (f' x) x)
    (hf' : IntervalIntegrable f' volume a b) (hperiod : f b = f a) :
    ‖fourierCoeffOn hab f n‖ ≤
      ((b - a) / (2 * Real.pi * |(n : ℝ)|)) * ‖fourierCoeffOn hab f' n‖ := by
  have hf_u : ∀ x, x ∈ uIcc a b → HasDerivAt f (f' x) x := by
    simpa [uIcc_of_le hab.le] using hf
  rw [fourierCoeffOn_of_hasDerivAt hab hn hf_u hf', hperiod, sub_self, mul_zero,
    zero_sub, norm_mul, norm_neg, norm_mul]
  have hden : -2 * Real.pi * Complex.I * (n : ℂ) =
      -2 * Real.pi * (Complex.I * (n : ℂ)) := by ring
  rw [hden]
  have hba : 0 < b - a := sub_pos.mpr hab
  have hba_complex : (b : ℂ) - a = (b - a : ℝ) := by
    norm_num
  rw [norm_div, norm_one, norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_I,
    Complex.norm_intCast, hba_complex, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hba]
  field_simp [ne_of_gt hba]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2, abs_of_pos Real.pi_pos]
  ring_nf
  exact le_rfl

theorem norm_fourierCoeffOn_le_of_derivative_chain
    {a b : ℝ} (hab : a < b) {f : ℕ → ℝ → ℂ} {m : ℕ} {n : ℤ} (hn : n ≠ 0)
    (hderiv : ∀ j < m, ∀ x, x ∈ Icc a b →
      HasDerivAt (f j) (f (j + 1) x) x)
    (hperiod : ∀ j < m, f j b = f j a)
    (hinterval : ∀ j, IntervalIntegrable (f j) volume a b) :
    ‖fourierCoeffOn hab (f 0) n‖ ≤
      ((b - a) / (2 * Real.pi * |(n : ℝ)|)) ^ m *
        ((b - a)⁻¹ * ∫ x in a..b, ‖f m x‖) := by
  let A : ℝ := (b - a) / (2 * Real.pi * |(n : ℝ)|)
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast hn
  have hA : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg (sub_pos.mpr hab).le
      (mul_nonneg (by positivity) (abs_nonneg _))
  have hchain : ∀ (k : ℕ) (g : ℕ → ℝ → ℂ),
      (∀ j < k, ∀ x, x ∈ Icc a b → HasDerivAt (g j) (g (j + 1) x) x) →
      (∀ j < k, g j b = g j a) →
      (∀ j, IntervalIntegrable (g j) volume a b) →
      ‖fourierCoeffOn hab (g 0) n‖ ≤ A ^ k * ‖fourierCoeffOn hab (g k) n‖ := by
    intro k
    induction k with
    | zero =>
        intro g _ _ _
        simp
    | succ k ih =>
        intro g hder hper hint
        have hstep := norm_fourierCoeffOn_le_of_hasDerivAt_coeff hab hn
          (hder 0 (Nat.zero_lt_succ k))
          (hint 1)
          (hper 0 (Nat.zero_lt_succ k))
        have htail := ih (fun j => g (j + 1)) (by
          intro j hj x hx
          simpa [Nat.add_assoc] using hder (j + 1) (by omega) x hx) (by
          intro j hj
          exact hper (j + 1) (by omega)) (by
          intro j
          exact hint (j + 1))
        calc
          ‖fourierCoeffOn hab (g 0) n‖ ≤ A *
              ‖fourierCoeffOn hab (g 1) n‖ := by simpa [A] using hstep
          _ ≤ A * (A ^ k * ‖fourierCoeffOn hab (g (k + 1)) n‖) :=
            mul_le_mul_of_nonneg_left htail hA
          _ = A ^ (k + 1) * ‖fourierCoeffOn hab (g (k + 1)) n‖ := by
            rw [pow_succ]
            ring
  have hchain' := hchain m f hderiv hperiod hinterval
  have hbase := norm_fourierCoeffOn_le_of_intervalIntegrable hab (f := f m) n
  calc
    ‖fourierCoeffOn hab (f 0) n‖ ≤ A ^ m * ‖fourierCoeffOn hab (f m) n‖ := hchain'
    _ ≤ A ^ m * ((b - a)⁻¹ * ∫ x in a..b, ‖f m x‖) :=
      mul_le_mul_of_nonneg_left hbase (pow_nonneg hA _)
    _ = ((b - a) / (2 * Real.pi * |(n : ℝ)|)) ^ m *
        ((b - a)⁻¹ * ∫ x in a..b, ‖f m x‖) := by rfl

end RegularityStructures.Phi43

end
