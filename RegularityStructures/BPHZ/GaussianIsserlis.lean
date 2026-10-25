/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.GaussianSteinProduct
public import RegularityStructures.BPHZ.GaussianMatchingsRecursion
public import RegularityStructures.BPHZ.WhiteNoiseChaosMomentsLinear
public import RegularityStructures.Probability.GaussianVector
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The general Isserlis theorem

For a centred Gaussian vector `X` with covariance `C` and `σ : Fin k → Fin n`,
`E[∏ₐ X_{σ a}] = ∑_{π perfect matching of Fin k} ∏_{pairs {a,b} of π} C_{σ a, σ b}`
(`integral_prod_eq_sum_perfectMatchings`).  A perfect matching of `ι` is a fixed-point-free
involution `π : ι → ι` (`perfectMatchings`); its pairs are `{c, π c}` with `c < π c`.  For odd `k`
the right-hand side is empty and the expectation vanishes (`integral_prod_eq_zero_of_odd`).

The proof is the induction on the number of factors given by the Gaussian integration by parts
`E[X_i ∏_{c ∈ t} X_{σ c}] = ∑_{b ∈ t} C_{i, σ b} E[∏_{c ∈ t \ {b}} X_{σ c}]`
(`integral_mul_prod_eq_sum`), matched with the pairing recursion `matchingSum_eq_sum_erase`.
-/

@[expose] public section

namespace RegularityStructures

/-- The perfect matchings of `ι`: fixed-point-free involutions `ι → ι`. -/
noncomputable def perfectMatchings (ι : Type*) [Fintype ι] : Finset (ι → ι) :=
  partialMatchings (Finset.univ : Finset ι)

end RegularityStructures

end

public section

open MeasureTheory

namespace RegularityStructures

theorem mem_perfectMatchings {ι : Type*} [Fintype ι] {π : ι → ι} :
    π ∈ perfectMatchings ι ↔ Function.Involutive π ∧ ∀ a, π a ≠ a := by
  simp [perfectMatchings, mem_partialMatchings]

namespace IsCentredGaussianVector

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} {X : Ω → Fin n → ℝ}
  {C : Fin n → Fin n → ℝ}

/-- Representation of the expectation of a continuous function of `X` through a symmetric square
root `A` of the covariance. -/
theorem exists_symm_integral_comp_eq (h : IsCentredGaussianVector P X C) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ, A.IsSymm ∧ A * A = C ∧ ∀ F : (Fin n → ℝ) → ℝ,
      Continuous F → ∫ ω, F (X ω) ∂P = ∫ z, F (A.mulVec z) ∂(standardGaussianMeasure n) := by
  obtain ⟨A, hsymm, hAA, hlaw⟩ := centredGaussianVector_standard_representation h
  have hAmeas : Measurable (Matrix.mulVecLin A) :=
    (LinearMap.continuous_of_finiteDimensional _).measurable
  refine ⟨A, hsymm, hAA, fun F hF => ?_⟩
  rw [← integral_map h.1 hF.aestronglyMeasurable, hlaw,
    integral_map hAmeas.aemeasurable hF.aestronglyMeasurable]
  rfl

/-- **Gaussian integration by parts for products.**
`E[X_i ∏_{c ∈ t} X_{σ c}] = ∑_{b ∈ t} C_{i, σ b} E[∏_{c ∈ t \ {b}} X_{σ c}]`. -/
theorem integral_mul_prod_eq_sum (h : IsCentredGaussianVector P X C) {ι : Type*}
    [DecidableEq ι] (i : Fin n) (σ : ι → Fin n) (t : Finset ι) :
    ∫ ω, X ω i * ∏ c ∈ t, X ω (σ c) ∂P =
      ∑ b ∈ t, C i (σ b) * ∫ ω, ∏ c ∈ t.erase b, X ω (σ c) ∂P := by
  obtain ⟨A, hsymm, hAA, hint⟩ := h.exists_symm_integral_comp_eq
  rw [hint (fun x => x i * ∏ c ∈ t, x (σ c)) (by fun_prop)]
  rw [integral_linearFormPoly_mul_prod]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hint (fun x => ∏ c ∈ t.erase b, x (σ c)) (by fun_prop)]
  congr 1
  rw [← hAA, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hsymm.apply j (σ b)]

/-- Products of coordinates of a centred Gaussian vector are integrable. -/
theorem integrable_prod_apply (h : IsCentredGaussianVector P X C) {ι : Type*} (σ : ι → Fin n)
    (t : Finset ι) : Integrable (fun ω => ∏ c ∈ t, X ω (σ c)) P := by
  simpa using integrable_eval_pow_of_isCentredGaussianVector h (∏ c ∈ t, (MvPolynomial.X (σ c) :
    MvPolynomial (Fin n) ℝ)) 1

/-- The Isserlis recursion for a finite set `s` of factors: the expectation of `∏_{c ∈ s} X_{σ c}`
is the sum over perfect matchings of `s` of the products of covariances of the pairs. -/
theorem integral_prod_eq_matchingSum (h : IsCentredGaussianVector P X C) {ι : Type*} [Fintype ι]
    [LinearOrder ι] (σ : ι → Fin n) (s : Finset ι) :
    ∫ ω, ∏ c ∈ s, X ω (σ c) ∂P = matchingSum (fun a b => C (σ a) (σ b)) s := by
  induction s using Finset.strongInduction with
  | H s ih =>
    have := h.isProbabilityMeasure
    rcases s.eq_empty_or_nonempty with rfl | hne
    · simp [matchingSum_empty]
    have ha := s.min'_mem hne
    rw [matchingSum_eq_sum_erase _ ha (fun b hb => s.min'_le b hb)]
    simp_rw [← Finset.mul_prod_erase s (fun c => X _ (σ c)) ha]
    rw [h.integral_mul_prod_eq_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [ih _ ?_]
    refine (Finset.erase_subset _ _).trans_ssubset ?_
    exact Finset.erase_ssubset ha

end IsCentredGaussianVector

end RegularityStructures

end
