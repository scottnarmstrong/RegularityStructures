/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.GaussianPolynomialHypercontractivity

/-!
# Equivalence of all even moments for Gaussian polynomials

The dyadic moment equivalence `exists_integral_eval_pow_le_of_totalDegree_le` extends to every even
exponent `2 p`: for `p ≤ N = 2^k` and `y, s ≥ 0` one has `y^p s^(N-p) ≤ s^N + y^N`
(`pow_mul_pow_le_pow_add_pow`), and integrating with `y = f²` and `s = E f²` (or `s → 0` if
`E f² = 0`) bounds the `2p`-th moment by `(1 + A) (E f²)^p`.
-/

public section

open MvPolynomial MeasureTheory

namespace RegularityStructures

variable {n : ℕ}

theorem pow_mul_pow_le_pow_add_pow {y s : ℝ} (hy : 0 ≤ y) (hs : 0 ≤ s) {p N : ℕ} (hpN : p ≤ N) :
    y ^ p * s ^ (N - p) ≤ s ^ N + y ^ N := by
  rcases le_total y s with h | h
  · have h1 : y ^ p * s ^ (N - p) ≤ s ^ p * s ^ (N - p) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hy h p) (by positivity)
    rw [← pow_add, Nat.add_sub_cancel' hpN] at h1
    have : 0 ≤ y ^ N := by positivity
    linarith
  · have h1 : y ^ p * s ^ (N - p) ≤ y ^ p * y ^ (N - p) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs h _) (by positivity)
    rw [← pow_add, Nat.add_sub_cancel' hpN] at h1
    have : 0 ≤ s ^ N := by positivity
    linarith

/-- Equivalence of every even moment of a Gaussian polynomial with a power of its variance,
uniformly in the dimension. -/
theorem exists_integral_eval_pow_two_mul_le_of_totalDegree_le (m p : ℕ) (hp : 1 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (n : ℕ) (f : MvPolynomial (Fin n) ℝ), f.totalDegree ≤ m →
      ∫ x, (MvPolynomial.eval x f) ^ (2 * p) ∂(standardGaussianMeasure n) ≤
        A * (∫ x, (MvPolynomial.eval x f) ^ 2 ∂(standardGaussianMeasure n)) ^ p := by
  have hpk : p ≤ 2 ^ p := (Nat.lt_two_pow_self).le
  obtain ⟨A0, hA0, hA⟩ := exists_integral_eval_pow_le_of_totalDegree_le m p
  set N : ℕ := 2 ^ p with hN
  refine ⟨1 + A0, by positivity, fun n f hf => ?_⟩
  set S : ℝ := ∫ x, eval x f ^ 2 ∂(standardGaussianMeasure n) with hS
  set I : ℝ := ∫ x, eval x f ^ (2 * p) ∂(standardGaussianMeasure n) with hI
  have hS0 : 0 ≤ S := integral_nonneg fun x => sq_nonneg _
  have hI0 : 0 ≤ I := integral_nonneg fun x => by rw [pow_mul]; positivity
  have hmom : ∫ x, eval x f ^ (2 ^ (p + 1)) ∂(standardGaussianMeasure n) ≤ A0 * S ^ N :=
    hA n f hf
  have hint : ∀ a : ℕ, Integrable (fun x => eval x f ^ a) (standardGaussianMeasure n) :=
    fun a => by simpa using integrable_eval_standardGaussianMeasure (f ^ a)
  have hN2 : 2 ^ (p + 1) = 2 * N := by rw [hN, pow_succ]; ring
  rw [hN2] at hmom
  -- the integrated pointwise inequality
  have key : ∀ s : ℝ, 0 ≤ s → s ^ (N - p) * I ≤ s ^ N + A0 * S ^ N := fun s hs => by
    have hpt : ∀ x : Fin n → ℝ, s ^ (N - p) * eval x f ^ (2 * p) ≤
        s ^ N + eval x f ^ (2 * N) := fun x => by
      have := pow_mul_pow_le_pow_add_pow (y := eval x f ^ 2) (sq_nonneg _) hs hpk
      simp only [← pow_mul] at this
      linarith
    calc s ^ (N - p) * I = ∫ x, s ^ (N - p) * eval x f ^ (2 * p) ∂(standardGaussianMeasure n) := by
          rw [hI, integral_const_mul]
      _ ≤ ∫ x, (s ^ N + eval x f ^ (2 * N)) ∂(standardGaussianMeasure n) :=
          integral_mono ((hint _).const_mul _) ((integrable_const _).add (hint _)) hpt
      _ = s ^ N + ∫ x, eval x f ^ (2 * N) ∂(standardGaussianMeasure n) := by
          rw [integral_add (integrable_const _) (hint _)]; simp
      _ ≤ s ^ N + A0 * S ^ N := add_le_add_right hmom _
  rcases hS0.eq_or_lt with hS00 | hSpos
  · -- degenerate case `S = 0`
    have hS' : S = 0 := hS00.symm
    have hle : ∀ s : ℝ, 0 < s → I ≤ s ^ p := fun s hs => by
      have h := key s hs.le
      rw [hS', zero_pow (by omega : N ≠ 0)] at h
      simp only [mul_zero, add_zero] at h
      have hpos : 0 < s ^ (N - p) := pow_pos hs _
      rw [← le_div_iff₀' hpos] at h
      calc I ≤ s ^ N / s ^ (N - p) := h
        _ = s ^ p := by
          have e : s ^ N = s ^ (N - p) * s ^ p := by rw [← pow_add, Nat.sub_add_cancel hpk]
          rw [e, mul_div_cancel_left₀ _ hpos.ne']
    rw [hS', zero_pow (by omega : p ≠ 0), mul_zero]
    by_contra hcon
    have hIpos : 0 < I := lt_of_not_ge fun h => hcon (le_antisymm h hI0 ▸ le_rfl)
    set s : ℝ := min 1 (I / 2) with hs
    have hs0 : 0 < s := lt_min one_pos (by positivity)
    have hs1 : s ≤ 1 := min_le_left _ _
    have hs2 : s ≤ I / 2 := min_le_right _ _
    have h1 := hle s hs0
    have h2 : s ^ p ≤ s := pow_le_of_le_one hs0.le hs1 (by omega)
    linarith
  · -- main case `S > 0`
    have h := key S hS0
    have hpos : 0 < S ^ (N - p) := pow_pos hSpos _
    have hSN : S ^ N = S ^ (N - p) * S ^ p := by rw [← pow_add, Nat.sub_add_cancel hpk]
    rw [hSN] at h
    have : S ^ (N - p) * I ≤ S ^ (N - p) * ((1 + A0) * S ^ p) := by
      calc S ^ (N - p) * I ≤ S ^ (N - p) * S ^ p + A0 * (S ^ (N - p) * S ^ p) := h
        _ = S ^ (N - p) * ((1 + A0) * S ^ p) := by ring
    exact le_of_mul_le_mul_left this hpos

end RegularityStructures

end
