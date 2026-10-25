/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Basic.Real.Basic

/-!
# Total degree and the Euler operator for multivariate polynomials

Algebraic input for the reverse Poincaré inequality for Gaussian polynomials:

* `totalDegree_le_iff_coeff`: the coefficient characterisation of `totalDegree p ≤ d`;
* `totalDegree_pderiv_le`, `pderiv_eq_zero_of_totalDegree_le_zero`: a partial derivative lowers the
  total degree by one;
* `eulerOp p = ∑ i, X i * pderiv i p`, the Euler operator, acts on the coefficient of `X^s` by
  multiplication with `|s|`, so `eulerOp p - (m + 1) • p` has total degree at most `m` whenever
  `p` has total degree at most `m + 1` (`totalDegree_eulerOp_sub_le`).
-/

@[expose] public noncomputable section

open MvPolynomial

namespace RegularityStructures

variable {n : ℕ}

/-- The Euler operator `p ↦ ∑ i, X i * ∂_i p`. -/
def eulerOp (p : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ i, X i * pderiv i p

end RegularityStructures

end

public section

open MvPolynomial

namespace RegularityStructures

variable {n : ℕ}

theorem totalDegree_le_iff_coeff {p : MvPolynomial (Fin n) ℝ} {d : ℕ} :
    p.totalDegree ≤ d ↔ ∀ s : Fin n →₀ ℕ, p.coeff s ≠ 0 → ∑ i, s i ≤ d := by
  rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
  refine forall_congr' fun s => ?_
  rw [mem_support_iff, Finsupp.sum_fintype _ _ (by simp)]

theorem totalDegree_pderiv_le {p : MvPolynomial (Fin n) ℝ} {d : ℕ} (i : Fin n)
    (hp : p.totalDegree ≤ d + 1) : (pderiv i p).totalDegree ≤ d := by
  rw [totalDegree_le_iff_coeff] at hp ⊢
  intro s hs
  rw [coeff_pderiv] at hs
  have h1 : p.coeff (s + Finsupp.single i 1) ≠ 0 := left_ne_zero_of_mul hs
  have h2 := hp _ h1
  have h3 : ∑ j, (s + Finsupp.single i 1 : Fin n →₀ ℕ) j = ∑ j, s j + 1 := by
    simp [Finset.sum_add_distrib, Finsupp.single_apply]
  omega

theorem pderiv_eq_zero_of_totalDegree_le_zero {p : MvPolynomial (Fin n) ℝ}
    (hp : p.totalDegree ≤ 0) (i : Fin n) : pderiv i p = 0 := by
  have h := totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp hp)
  rw [h, pderiv_C]

theorem totalDegree_pderiv_le_of_le {p : MvPolynomial (Fin n) ℝ} {d : ℕ}
    (hp : p.totalDegree ≤ d) (i : Fin n) : (pderiv i p).totalDegree ≤ d - 1 := by
  rcases d with _ | d
  · rw [pderiv_eq_zero_of_totalDegree_le_zero hp i]
    simp
  · exact totalDegree_pderiv_le i hp

private theorem eulerOp_monomial (s : Fin n →₀ ℕ) (c : ℝ) :
    eulerOp (monomial s c) = (∑ i, s i) • monomial s c := by
  unfold eulerOp
  simp_rw [X_mul_pderiv_monomial]
  rw [Finset.sum_smul]

private theorem eulerOp_add (p q : MvPolynomial (Fin n) ℝ) :
    eulerOp (p + q) = eulerOp p + eulerOp q := by
  unfold eulerOp
  simp [mul_add, Finset.sum_add_distrib]

theorem coeff_eulerOp (p : MvPolynomial (Fin n) ℝ) (s : Fin n →₀ ℕ) :
    (eulerOp p).coeff s = (∑ i, s i : ℕ) * p.coeff s := by
  induction p using MvPolynomial.induction_on' with
  | monomial t c =>
    rw [eulerOp_monomial, coeff_smul, coeff_monomial, nsmul_eq_mul]
    by_cases h : t = s
    · subst h; simp
    · simp [h]
  | add p q hp hq =>
    rw [eulerOp_add]
    change (eulerOp p).coeff s + (eulerOp q).coeff s = _ * (p.coeff s + q.coeff s)
    rw [hp, hq, mul_add]

theorem totalDegree_eulerOp_sub_le {p : MvPolynomial (Fin n) ℝ} {m : ℕ}
    (hp : p.totalDegree ≤ m + 1) :
    (eulerOp p - ((m + 1 : ℕ) : ℝ) • p).totalDegree ≤ m := by
  rw [totalDegree_le_iff_coeff] at hp ⊢
  intro s hs
  rw [coeff_sub, coeff_smul, coeff_eulerOp, smul_eq_mul] at hs
  have h1 : p.coeff s ≠ 0 := by
    intro h; apply hs; simp [h]
  have h2 := hp s h1
  by_contra hlt
  have h3 : ∑ i, s i = m + 1 := by omega
  apply hs
  rw [h3]
  ring

end RegularityStructures

end
