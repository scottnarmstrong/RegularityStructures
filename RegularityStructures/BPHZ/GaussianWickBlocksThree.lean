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

/-!
# Three Wick monomials: the counterterm cross terms

`E[:X_a^3: :X_b^2: X_d] = 6 C_ab² C_ad` (pairing `d` with one of the three `a`s and the
remaining two `a`s with the two `b`s).  The proof evaluates the list recursion `listMatchSum`
on the tagged letters.
-/

public section

open MeasureTheory

namespace RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} {X : Ω → Fin n → ℝ}
  {C : Fin n → Fin n → ℝ}

/-- The diagram formula for three words. -/
theorem integral_wick_mul_wick_mul_wick_eq (h : IsCentredGaussianVector P X C)
    (l₀ l₁ l₂ : List (Fin n)) :
    ∫ ω, wickMonomial C l₀ (X ω) * wickMonomial C l₁ (X ω) * wickMonomial C l₂ (X ω) ∂P =
      listMatchSum (taggedWeight C) (taggedLetters ![l₀, l₁, l₂]) := by
  have := integral_prod_wickMonomial_eq_listMatchSum_tagged h ![l₀, l₁, l₂]
  simpa [Fin.prod_univ_three, mul_assoc] using this

/-- **(W5)** `E[:X_a^3: :X_b^2: X_d] = 6 C_ab² C_ad`. -/
theorem integral_wick_three_mul_wick_two_mul_X (h : IsCentredGaussianVector P X C)
    (a b d : Fin n) :
    ∫ ω, wickMonomial C (List.replicate 3 a) (X ω) * wickMonomial C (List.replicate 2 b) (X ω) *
        X ω d ∂P = 6 * C a b ^ 2 * C a d := by
  have := integral_wick_mul_wick_mul_wick_eq h (List.replicate 3 a) (List.replicate 2 b) [d]
  simp only [wickMonomial_singleton] at this
  rw [this]
  simp [taggedLetters, List.finRange_succ, listMatchSum_cons_picks, listMatchSum_nil, picks,
    taggedWeight, List.replicate]
  ring

end RegularityStructures

end
