/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Coefficients of translated monomials

The coefficient of `X^l` in `(X + h)^k = ∏ᵢ (Xᵢ + hᵢ)^{kᵢ}` is `∏ᵢ binom(kᵢ, lᵢ) hᵢ^{kᵢ - lᵢ}` if
`l ≤ k` and `0` otherwise (`coeff_prod_X_add_C_pow`).
-/

public section

namespace RegularityStructures

open MvPolynomial

theorem X_add_C_pow_eq_sum (i : Fin 4) (a : ℝ) (n : ℕ) :
    (X i + C a : MvPolynomial (Fin 4) ℝ) ^ n =
      ∑ m ∈ Finset.range (n + 1),
        monomial (Finsupp.single i m) (a ^ (n - m) * (n.choose m : ℝ)) := by
  rw [add_pow]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [X_pow_eq_monomial, ← C_pow, ← map_natCast (C : ℝ →+* MvPolynomial (Fin 4) ℝ), mul_assoc,
    ← C_mul]
  rw [mul_comm, C_mul_monomial, mul_one]

theorem coeff_prod_X_add_C_pow (h : Fin 4 → ℝ) (k l : Fin 4 →₀ ℕ) :
    (∏ i, (X i + C (h i) : MvPolynomial (Fin 4) ℝ) ^ k i).coeff l =
      if l ≤ k then ∏ i, h i ^ (k i - l i) * ((k i).choose (l i) : ℝ) else 0 := by
  simp_rw [X_add_C_pow_eq_sum]
  rw [Finset.prod_univ_sum, coeff_sum]
  have hterm : ∀ p : Fin 4 → ℕ,
      (∏ i, monomial (Finsupp.single i (p i)) (h i ^ (k i - p i) * ((k i).choose (p i) : ℝ)) :
        MvPolynomial (Fin 4) ℝ) =
      monomial (Finsupp.equivFunOnFinite.symm p)
        (∏ i, h i ^ (k i - p i) * ((k i).choose (p i) : ℝ)) := by
    intro p
    have hs : ∑ i, Finsupp.single i (p i) = Finsupp.equivFunOnFinite.symm p :=
      Finsupp.ext fun j => by simp [Finsupp.finsetSum_apply, Finsupp.single_apply]
    rw [← monomial_sum_prod, hs]
  simp_rw [hterm, coeff_monomial]
  split_ifs with hl
  · rw [Finset.sum_eq_single (⇑l)]
    · simp
    · intro p _ hp
      rw [ite_eq_right_iff]
      intro e
      exact absurd (by simpa using congrArg (⇑) e) hp
    · intro hn
      exact absurd (Fintype.mem_piFinset.2 fun i =>
        Finset.mem_range.2 (Nat.lt_succ_of_le (hl i))) hn
  · refine Finset.sum_eq_zero fun p hp => ?_
    rw [ite_eq_right_iff]
    intro e
    exfalso
    apply hl
    intro i
    have := Fintype.mem_piFinset.1 hp i
    have e' : p i = l i := by simpa using congrFun (congrArg (⇑) e) i
    rw [← e']
    exact Nat.lt_succ_iff.1 (Finset.mem_range.1 this)

end RegularityStructures

end
