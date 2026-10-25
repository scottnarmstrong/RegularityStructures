/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.GaussianWickMonomial
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin

/-!
# Low-order Wick monomials

`wickMonomial C [i] x = x i`, `wickMonomial C [i, i] x = x i ^ 2 - C i i` and
`wickMonomial C [i, i, i] x = x i ^ 3 - 3 * C i i * x i`.
-/

public section

namespace RegularityStructures

theorem involutions_fin_one : involutions (Fin 1) = {id} := by
  decide +kernel

theorem involutions_fin_two : involutions (Fin 2) = {id, ![1, 0]} := by
  decide +kernel

theorem involutions_fin_three :
    involutions (Fin 3) = {id, ![1, 0, 2], ![2, 1, 0], ![0, 2, 1]} := by
  decide +kernel

theorem wickMonomial_singleton {n : ℕ} (C : Fin n → Fin n → ℝ) (i : Fin n) (x : Fin n → ℝ) :
    wickMonomial C [i] x = x i := by
  show ∑ π ∈ involutions (Fin 1), (-1) ^ (pairSet π).card *
    (matchingWeight (fun a b => C ([i].get a) ([i].get b)) π *
      ∏ c ∈ fixedSet π, x ([i].get c)) = x i
  rw [involutions_fin_one]
  simp [pairSet, fixedSet, matchingWeight_eq_prod_pairSet]

theorem wickMonomial_pair_self {n : ℕ} (C : Fin n → Fin n → ℝ) (i : Fin n) (x : Fin n → ℝ) :
    wickMonomial C [i, i] x = x i ^ 2 - C i i := by
  show ∑ π ∈ involutions (Fin 2), (-1) ^ (pairSet π).card *
    (matchingWeight (fun a b => C ([i, i].get a) ([i, i].get b)) π *
      ∏ c ∈ fixedSet π, x ([i, i].get c)) = x i ^ 2 - C i i
  rw [involutions_fin_two, Finset.sum_pair (by decide)]
  have h1 : pairSet (id : Fin 2 → Fin 2) = ∅ := by
    ext c; simp [pairSet]
  have h2 : pairSet (![1, 0] : Fin 2 → Fin 2) = {0} := by
    ext c; fin_cases c <;> simp [pairSet]
  have h3 : fixedSet (id : Fin 2 → Fin 2) = Finset.univ := by
    ext c; simp [fixedSet]
  have h4 : fixedSet (![1, 0] : Fin 2 → Fin 2) = ∅ := by
    ext c; fin_cases c <;> simp [fixedSet]
  simp [h1, h2, h3, h4, matchingWeight_eq_prod_pairSet, Fin.prod_univ_two, sq]
  ring

theorem wickMonomial_triple_self {n : ℕ} (C : Fin n → Fin n → ℝ) (i : Fin n)
    (x : Fin n → ℝ) : wickMonomial C [i, i, i] x = x i ^ 3 - 3 * C i i * x i := by
  show ∑ π ∈ involutions (Fin 3), (-1) ^ (pairSet π).card *
    (matchingWeight (fun a b => C ([i, i, i].get a) ([i, i, i].get b)) π *
      ∏ c ∈ fixedSet π, x ([i, i, i].get c)) = x i ^ 3 - 3 * C i i * x i
  rw [involutions_fin_three]
  have e1 : (![1, 0, 2] : Fin 3 → Fin 3) ∉ ({![2, 1, 0], ![0, 2, 1]} : Finset (Fin 3 → Fin 3)) := by
    decide +kernel
  have e2 : (![2, 1, 0] : Fin 3 → Fin 3) ∉ ({![0, 2, 1]} : Finset (Fin 3 → Fin 3)) := by
    decide +kernel
  have e3 : (id : Fin 3 → Fin 3) ∉
      ({![1, 0, 2], ![2, 1, 0], ![0, 2, 1]} : Finset (Fin 3 → Fin 3)) := by
    decide +kernel
  rw [Finset.sum_insert e3, Finset.sum_insert e1, Finset.sum_insert e2, Finset.sum_singleton]
  have p1 : pairSet (id : Fin 3 → Fin 3) = ∅ := by
    ext c; simp [pairSet]
  have p2 : pairSet (![1, 0, 2] : Fin 3 → Fin 3) = {0} := by
    ext c; fin_cases c <;> simp [pairSet]
  have p3 : pairSet (![2, 1, 0] : Fin 3 → Fin 3) = {0} := by
    ext c; fin_cases c <;> simp [pairSet]
  have p4 : pairSet (![0, 2, 1] : Fin 3 → Fin 3) = {1} := by
    ext c; fin_cases c <;> simp [pairSet]
  have f1 : fixedSet (id : Fin 3 → Fin 3) = Finset.univ := by
    ext c; simp [fixedSet]
  have f2 : fixedSet (![1, 0, 2] : Fin 3 → Fin 3) = {2} := by
    ext c; fin_cases c <;> simp [fixedSet]
  have f3 : fixedSet (![2, 1, 0] : Fin 3 → Fin 3) = {1} := by
    ext c; fin_cases c <;> simp [fixedSet]
  have f4 : fixedSet (![0, 2, 1] : Fin 3 → Fin 3) = {0} := by
    ext c; fin_cases c <;> simp [fixedSet]
  simp [p1, p2, p3, p4, f1, f2, f3, f4, matchingWeight_eq_prod_pairSet, Fin.prod_univ_three]
  ring

end RegularityStructures

end
