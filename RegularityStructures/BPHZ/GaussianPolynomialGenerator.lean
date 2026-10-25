/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.GaussianPolynomialDegree
public import RegularityStructures.BPHZ.GaussianPolynomialIBP

/-!
# The Ornstein--Uhlenbeck generator on Gaussian polynomials

For polynomials in `n` variables, the Gaussian expectation `gaussExp p = ∫ eval x p dγ` is a linear
functional, and the Ornstein--Uhlenbeck generator is
`gaussGen f = ∑ i, (X i * ∂_i f - ∂_i ∂_i f)`.  Gaussian integration by parts gives the Dirichlet
form identity `∑ i, E[∂_i f ∂_i g] = E[f * gaussGen g]` (`sum_gaussExp_pderiv_mul_pderiv`), so
`gaussGen` is symmetric.  The Euler identity shows that `gaussGen f - (m + 1) f` has degree at most
`m` when `f` has degree at most `m + 1` (`totalDegree_gaussGen_sub_le`).
-/

@[expose] public noncomputable section

open MvPolynomial MeasureTheory

namespace RegularityStructures

/-- The Gaussian expectation of a polynomial. -/
def gaussExp {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : ℝ :=
  ∫ x, eval x p ∂(standardGaussianMeasure n)

/-- The Ornstein--Uhlenbeck generator `f ↦ ∑ i, (X i * ∂_i f - ∂_i ∂_i f)` on polynomials. -/
def gaussGen {n : ℕ} : MvPolynomial (Fin n) ℝ →ₗ[ℝ] MvPolynomial (Fin n) ℝ :=
  ∑ i : Fin n, ((LinearMap.mulLeft ℝ (X i : MvPolynomial (Fin n) ℝ)) ∘ₗ (pderiv i).toLinearMap -
    (pderiv i).toLinearMap ∘ₗ (pderiv i).toLinearMap)

end RegularityStructures

end

public section

open MvPolynomial MeasureTheory

namespace RegularityStructures

variable {n : ℕ}

theorem gaussExp_add (p q : MvPolynomial (Fin n) ℝ) :
    gaussExp (p + q) = gaussExp p + gaussExp q := by
  unfold gaussExp
  simp_rw [map_add]
  exact integral_add (integrable_eval_standardGaussianMeasure p)
    (integrable_eval_standardGaussianMeasure q)

theorem gaussExp_smul (c : ℝ) (p : MvPolynomial (Fin n) ℝ) :
    gaussExp (c • p) = c * gaussExp p := by
  unfold gaussExp
  simp_rw [smul_eval]
  exact integral_const_mul c _

theorem gaussExp_sub (p q : MvPolynomial (Fin n) ℝ) :
    gaussExp (p - q) = gaussExp p - gaussExp q := by
  have h := gaussExp_add (p - q) q
  rw [sub_add_cancel] at h
  linarith

theorem gaussExp_finset_sum {ι : Type*} (s : Finset ι) (p : ι → MvPolynomial (Fin n) ℝ) :
    gaussExp (∑ i ∈ s, p i) = ∑ i ∈ s, gaussExp (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [gaussExp]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, gaussExp_add, ih]

theorem gaussExp_sq_nonneg (p : MvPolynomial (Fin n) ℝ) : 0 ≤ gaussExp (p * p) := by
  unfold gaussExp
  exact integral_nonneg fun x => by rw [map_mul]; exact mul_self_nonneg _

theorem gaussGen_apply (f : MvPolynomial (Fin n) ℝ) :
    gaussGen f = ∑ i, (X i * pderiv i f - pderiv i (pderiv i f)) := by
  unfold gaussGen
  simp

theorem gaussGen_eq_eulerOp_sub (f : MvPolynomial (Fin n) ℝ) :
    gaussGen f = eulerOp f - ∑ i, pderiv i (pderiv i f) := by
  rw [gaussGen_apply, Finset.sum_sub_distrib]
  rfl

/-- The Dirichlet form of two polynomials, as a Gaussian expectation. -/
theorem gaussExp_pderiv_mul_pderiv (i : Fin n) (f g : MvPolynomial (Fin n) ℝ) :
    gaussExp (pderiv i f * pderiv i g) =
      gaussExp (f * (X i * pderiv i g - pderiv i (pderiv i g))) := by
  have h := integral_eval_X_mul_eq_pderiv i (f * pderiv i g)
  have h' : gaussExp (X i * (f * pderiv i g)) = gaussExp (pderiv i (f * pderiv i g)) := h
  rw [pderiv_mul, gaussExp_add] at h'
  have : f * (X i * pderiv i g - pderiv i (pderiv i g)) =
      X i * (f * pderiv i g) - f * pderiv i (pderiv i g) := by ring
  rw [this, gaussExp_sub, h']
  ring

/-- Gaussian integration by parts in Dirichlet form: `E[∇f · ∇g] = E[f L g]`. -/
theorem sum_gaussExp_pderiv_mul_pderiv (f g : MvPolynomial (Fin n) ℝ) :
    ∑ i, gaussExp (pderiv i f * pderiv i g) = gaussExp (f * gaussGen g) := by
  rw [gaussGen_apply, Finset.mul_sum, gaussExp_finset_sum]
  exact Finset.sum_congr rfl fun i _ => gaussExp_pderiv_mul_pderiv i f g

theorem gaussExp_mul_gaussGen_comm (f g : MvPolynomial (Fin n) ℝ) :
    gaussExp (f * gaussGen g) = gaussExp (g * gaussGen f) := by
  rw [← sum_gaussExp_pderiv_mul_pderiv, ← sum_gaussExp_pderiv_mul_pderiv]
  simp_rw [mul_comm (pderiv _ g)]

theorem totalDegree_eulerOp_le {f : MvPolynomial (Fin n) ℝ} {m : ℕ} (hf : f.totalDegree ≤ m) :
    (eulerOp f).totalDegree ≤ m := by
  rw [totalDegree_le_iff_coeff] at hf ⊢
  intro s hs
  rw [coeff_eulerOp] at hs
  exact hf s (right_ne_zero_of_mul hs)

theorem totalDegree_lap_le_pred {f : MvPolynomial (Fin n) ℝ} {m : ℕ} (hf : f.totalDegree ≤ m) :
    (∑ i, pderiv i (pderiv i f)).totalDegree ≤ m - 1 := by
  refine totalDegree_finsetSum_le fun i _ => ?_
  have h1 := totalDegree_pderiv_le_of_le hf i
  have h2 := totalDegree_pderiv_le_of_le h1 i
  omega

theorem totalDegree_lap_le {f : MvPolynomial (Fin n) ℝ} {m : ℕ} (hf : f.totalDegree ≤ m) :
    (∑ i, pderiv i (pderiv i f)).totalDegree ≤ m :=
  (totalDegree_lap_le_pred hf).trans (Nat.sub_le m 1)

theorem totalDegree_gaussGen_le {f : MvPolynomial (Fin n) ℝ} {m : ℕ} (hf : f.totalDegree ≤ m) :
    (gaussGen f).totalDegree ≤ m := by
  rw [gaussGen_eq_eulerOp_sub, sub_eq_add_neg]
  refine (totalDegree_add _ _).trans (max_le (totalDegree_eulerOp_le hf) ?_)
  rw [totalDegree_neg]
  exact totalDegree_lap_le hf

theorem totalDegree_gaussGen_sub_le {f : MvPolynomial (Fin n) ℝ} {m : ℕ}
    (hf : f.totalDegree ≤ m + 1) :
    (gaussGen f - ((m + 1 : ℕ) : ℝ) • f).totalDegree ≤ m := by
  have h : gaussGen f - ((m + 1 : ℕ) : ℝ) • f =
      (eulerOp f - ((m + 1 : ℕ) : ℝ) • f) + -(∑ i, pderiv i (pderiv i f)) := by
    rw [gaussGen_eq_eulerOp_sub]; ring
  rw [h]
  refine (totalDegree_add _ _).trans (max_le (totalDegree_eulerOp_sub_le hf) ?_)
  rw [totalDegree_neg]
  have := totalDegree_lap_le_pred hf
  omega

end RegularityStructures

end
