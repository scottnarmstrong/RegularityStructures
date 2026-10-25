/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.GaussianWickBlocksPositions
public import RegularityStructures.BPHZ.GaussianWickMonomialSpecial
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# Two Wick monomials

For a centred Gaussian vector with covariance `C`,
`E[:X_a^k: :X_b^l:] = k! * C a b ^ k` if `k = l` and `0` otherwise, for `k, l ≤ 3`
(`integral_wick_replicate_mul_wick_replicate`), and the first mixed expectation is
`E[X_b X_d] = C b d`.  The proofs evaluate the list recursion `listMatchSum` on the tagged
letters.
-/

public section

open MeasureTheory

namespace RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} {X : Ω → Fin n → ℝ}
  {C : Fin n → Fin n → ℝ}

/-- The diagram formula for two words. -/
theorem integral_wick_mul_wick_eq (h : IsCentredGaussianVector P X C) (l₀ l₁ : List (Fin n)) :
    ∫ ω, wickMonomial C l₀ (X ω) * wickMonomial C l₁ (X ω) ∂P =
      listMatchSum (taggedWeight C) (taggedLetters ![l₀, l₁]) := by
  have := integral_prod_wickMonomial_eq_listMatchSum_tagged h ![l₀, l₁]
  simpa [Fin.prod_univ_two] using this

/-- `E[:X_a^k: :X_b^l:] = k! C_ab^k` if `k = l` and `0` otherwise, for `k, l ≤ 3`. -/
theorem integral_wick_replicate_mul_wick_replicate (h : IsCentredGaussianVector P X C)
    (a b : Fin n) {k l : ℕ} (hk : k ≤ 3) (hl : l ≤ 3) :
    ∫ ω, wickMonomial C (List.replicate k a) (X ω) *
        wickMonomial C (List.replicate l b) (X ω) ∂P =
      if k = l then (k.factorial : ℝ) * C a b ^ k else 0 := by
  rw [integral_wick_mul_wick_eq h]
  interval_cases k <;> interval_cases l <;>
    simp [taggedLetters, List.finRange_succ, listMatchSum_cons_picks, listMatchSum_nil, picks,
      taggedWeight, List.replicate] <;> ring

end RegularityStructures

end
