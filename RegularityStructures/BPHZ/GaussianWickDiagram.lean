/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.GaussianWickProduct
public import RegularityStructures.BPHZ.GaussianIsserlis
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The diagram formula for products of Wick monomials

For a centred Gaussian vector `X` with covariance `C` and words `L : Fin r → List (Fin n)`,

`E[∏ⱼ :X^{L j}:] = ∑_{ρ} ∏_{pairs {c, ρ c}} C_{letter c, letter (ρ c)}`

where `ρ` runs over the perfect matchings of the positions `WickPosition L` having no pair inside a
single block (`integral_prod_wickMonomial_eq_sum_matchings`); every such product is integrable
(`integrable_prod_wickMonomial`).

The proof expands the product as a sum over block involutions
(`prod_wickMonomial_eq_sum_blockInvolutions`), integrates the unmatched factors with the Isserlis
theorem (`integral_prod_eq_matchingSum`), and resolves the signs by
`sum_blockInvolutions_matchingSum`.
-/

public section

open MeasureTheory

namespace RegularityStructures

namespace IsCentredGaussianVector

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} {X : Ω → Fin n → ℝ}
  {C : Fin n → Fin n → ℝ}

/-- Every product of Wick monomials of a centred Gaussian vector is integrable. -/
theorem integrable_prod_wickMonomial (h : IsCentredGaussianVector P X C) {r : ℕ}
    (L : Fin r → List (Fin n)) :
    Integrable (fun ω => ∏ j, wickMonomial C (L j) (X ω)) P := by
  simp_rw [prod_wickMonomial_eq_sum_blockInvolutions]
  refine integrable_finsetSum _ fun π _ => ?_
  have := h.integrable_prod_apply (fun c : WickPosition L => c.letter) (fixedSet π)
  exact (this.const_mul _).const_mul _

end IsCentredGaussianVector

/-- **Diagram formula** (Hairer, *A theory of regularity structures*, Lemma 10.3, for a finite
Gaussian vector). The expectation of a product of Wick monomials `:X^{L j}:` is the sum, over the
perfect matchings `ρ` of the positions of the words having no pair inside a single word, of the
product over the pairs `{c, ρ c}` (`c < ρ c`) of the covariances of the letters. -/
theorem integral_prod_wickMonomial_eq_sum_matchings {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {n : ℕ} {X : Ω → Fin n → ℝ} {C : Fin n → Fin n → ℝ}
    (h : IsCentredGaussianVector P X C) {r : ℕ} (L : Fin r → List (Fin n)) :
    ∫ ω, ∏ j, wickMonomial C (L j) (X ω) ∂P =
      ∑ ρ ∈ (perfectMatchings (WickPosition L)).filter
          (fun ρ => ∀ c, (ρ c).block ≠ c.block),
        ∏ c ∈ Finset.univ.filter fun c => c < ρ c, C c.letter (ρ c).letter := by
  have hint : ∀ π ∈ blockInvolutions (fun c : WickPosition L => c.block),
      Integrable (fun ω => (-1 : ℝ) ^ (pairSet π).card *
        (matchingWeight (fun a b : WickPosition L => C a.letter b.letter) π *
          ∏ c ∈ fixedSet π, X ω c.letter)) P := fun π _ =>
    ((h.integrable_prod_apply (fun c : WickPosition L => c.letter) (fixedSet π)).const_mul
      _).const_mul _
  simp_rw [prod_wickMonomial_eq_sum_blockInvolutions]
  rw [integral_finsetSum _ hint]
  have hterm : ∀ π ∈ blockInvolutions (fun c : WickPosition L => c.block),
      ∫ ω, (-1 : ℝ) ^ (pairSet π).card *
        (matchingWeight (fun a b : WickPosition L => C a.letter b.letter) π *
          ∏ c ∈ fixedSet π, X ω c.letter) ∂P =
      (-1 : ℝ) ^ (pairSet π).card *
        (matchingWeight (fun a b : WickPosition L => C a.letter b.letter) π *
          matchingSum (fun a b : WickPosition L => C a.letter b.letter) (fixedSet π)) := by
    intro π _
    rw [integral_const_mul, integral_const_mul,
      h.integral_prod_eq_matchingSum (fun c : WickPosition L => c.letter) (fixedSet π)]
  rw [Finset.sum_congr rfl hterm,
    sum_blockInvolutions_matchingSum (fun c : WickPosition L => c.block)]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  exact Finset.prod_congr (by ext; simp) fun _ _ => rfl

end RegularityStructures

end
