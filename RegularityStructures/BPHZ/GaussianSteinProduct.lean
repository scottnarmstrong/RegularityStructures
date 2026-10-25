/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.GaussianPolynomialIBP
public import RegularityStructures.Probability.MalliavinClosureLaw
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Gaussian integration by parts for products of coordinates

For a centred Gaussian vector `X` with covariance `C`, a finite family of coordinates
`σ : ι → Fin n`, and `t : Finset ι`,
`E[X_i ∏_{c ∈ t} X_{σ c}] = ∑_{b ∈ t} C_{i, σ b} E[∏_{c ∈ t \ {b}} X_{σ c}]`
(`IsCentredGaussianVector.integral_mul_prod_eq_sum`).

The proof writes `X = A Z` in law, with `A` symmetric, `A * A = C` and `Z` standard Gaussian, so
that `∏_{c ∈ t} X_{σ c}` becomes a polynomial in `Z`, and applies the polynomial integration by
parts `E[Z_j F] = E[∂_j F]` (`integral_eval_X_mul_eq_pderiv`) together with the Leibniz rule.
-/

public section

open MeasureTheory MvPolynomial

namespace RegularityStructures

variable {ι : Type*} [DecidableEq ι] {n : ℕ}

/-- The Leibniz rule for the partial derivative of a finite product. -/
theorem pderiv_finset_prod (j : Fin n) (g : ι → MvPolynomial (Fin n) ℝ) (t : Finset ι) :
    pderiv j (∏ c ∈ t, g c) = ∑ b ∈ t, pderiv j (g b) * ∏ c ∈ t.erase b, g c := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, pderiv_mul, ih, Finset.sum_insert ha, Finset.erase_insert ha,
      Finset.mul_sum]
    have : ∀ b ∈ t, pderiv j (g b) * ∏ c ∈ (insert a t).erase b, g c =
        g a * (pderiv j (g b) * ∏ c ∈ t.erase b, g c) := by
      intro b hb
      have hba : b ≠ a := fun h => ha (h ▸ hb)
      rw [Finset.erase_insert_of_ne (Ne.symm hba), Finset.prod_insert (fun h =>
        ha (Finset.mem_of_mem_erase h))]
      ring
    rw [Finset.sum_congr rfl this]

/-- The linear form `z ↦ (A z)ₖ` as a polynomial. -/
noncomputable def linearFormPoly (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    MvPolynomial (Fin n) ℝ :=
  ∑ j, C (A k j) * X j

theorem eval_linearFormPoly (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) (z : Fin n → ℝ) :
    eval z (linearFormPoly A k) = A.mulVec z k := by
  simp [linearFormPoly, Matrix.mulVec, dotProduct]

theorem pderiv_linearFormPoly (A : Matrix (Fin n) (Fin n) ℝ) (k j : Fin n) :
    pderiv j (linearFormPoly A k) = C (A k j) := by
  classical
  simp [linearFormPoly, pderiv_X, Pi.single_apply]

/-- Gaussian integration by parts for a product of linear forms of a standard Gaussian. -/
theorem integral_linearFormPoly_mul_prod (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n)
    (σ : ι → Fin n) (t : Finset ι) :
    ∫ z, A.mulVec z i * ∏ c ∈ t, A.mulVec z (σ c) ∂(standardGaussianMeasure n) =
      ∑ b ∈ t, (∑ j, A i j * A (σ b) j) *
        ∫ z, ∏ c ∈ t.erase b, A.mulVec z (σ c) ∂(standardGaussianMeasure n) := by
  set G : MvPolynomial (Fin n) ℝ := ∏ c ∈ t, linearFormPoly A (σ c) with hG
  have hL : ∀ z : Fin n → ℝ, A.mulVec z i * ∏ c ∈ t, A.mulVec z (σ c) =
      ∑ j, A i j * eval z (X j * G) := by
    intro z
    simp only [hG, map_mul, eval_X, map_prod, eval_linearFormPoly, Matrix.mulVec, dotProduct]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hint : ∀ j, Integrable (fun z => eval z (X j * G)) (standardGaussianMeasure n) :=
    fun j => integrable_eval_standardGaussianMeasure _
  simp_rw [hL]
  rw [integral_finsetSum _ fun j _ => (hint j).const_mul _]
  simp_rw [integral_const_mul, integral_eval_X_mul_eq_pderiv, hG, pderiv_finset_prod,
    pderiv_linearFormPoly, map_sum]
  have hR : ∀ (b : ι) (z : Fin n → ℝ), eval z (∏ c ∈ t.erase b, linearFormPoly A (σ c)) =
      ∏ c ∈ t.erase b, A.mulVec z (σ c) := by
    intro b z
    simp [map_prod, eval_linearFormPoly]
  have hi : ∀ (j : Fin n) (b : ι), Integrable (fun z => eval z (C (A (σ b) j) *
      ∏ c ∈ t.erase b, linearFormPoly A (σ c))) (standardGaussianMeasure n) :=
    fun j b => integrable_eval_standardGaussianMeasure _
  simp_rw [integral_finsetSum _ fun b _ => hi _ b]
  simp_rw [map_mul, eval_C, hR, integral_const_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end RegularityStructures

end
