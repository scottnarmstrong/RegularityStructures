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
# Four Wick monomials: the block patterns of the `Φ⁴₃` trees

For a centred Gaussian vector with covariance `C` and indices `a b c d`:

* `E[:X_a^3: X_b :X_c^3: X_d] = 18 C_ab C_ac² C_cd + 6 C_ac³ C_bd + 18 C_ac² C_ad C_bc`;
* `E[:X_a^2: :X_b^2: :X_c^2: :X_d^2:] = 4 C_ab² C_cd² + 4 C_ac² C_bd² + 4 C_ad² C_bc²
  + 16 (C_ab C_ac C_bd C_cd + C_ab C_ad C_bc C_cd + C_ac C_ad C_bc C_bd)`;
* `E[:X_a^3: :X_b^2: :X_c^3: :X_d^2:] = 36 C_ab² C_ac C_cd² + 72 C_ab C_ac² C_bd C_cd
  + 144 C_ab C_ac C_ad C_bc C_cd + 12 C_ac³ C_bd² + 72 C_ac² C_ad C_bc C_bd
  + 36 C_ac C_ad² C_bc²`.

Each pair of positions is oriented from the earlier block to the later one, so no symmetry of `C`
is needed.  The proofs evaluate the list recursion `listMatchSum` on the tagged letters.
-/

public section

open MeasureTheory

namespace RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} {X : Ω → Fin n → ℝ}
  {C : Fin n → Fin n → ℝ}

/-- The diagram formula for four words. -/
theorem integral_wick_mul_wick_mul_wick_mul_wick_eq (h : IsCentredGaussianVector P X C)
    (l₀ l₁ l₂ l₃ : List (Fin n)) :
    ∫ ω, wickMonomial C l₀ (X ω) * wickMonomial C l₁ (X ω) * wickMonomial C l₂ (X ω) *
        wickMonomial C l₃ (X ω) ∂P =
      listMatchSum (taggedWeight C) (taggedLetters ![l₀, l₁, l₂, l₃]) := by
  have := integral_prod_wickMonomial_eq_listMatchSum_tagged h ![l₀, l₁, l₂, l₃]
  simpa [Fin.prod_univ_four, mul_assoc] using this

/-- **(W2)** `E[:X_a^3: X_b :X_c^3: X_d]`. -/
theorem integral_wick_three_mul_X_mul_wick_three_mul_X (h : IsCentredGaussianVector P X C)
    (a b c d : Fin n) :
    ∫ ω, wickMonomial C (List.replicate 3 a) (X ω) * X ω b *
        wickMonomial C (List.replicate 3 c) (X ω) * X ω d ∂P =
      18 * C a b * C a c ^ 2 * C c d + 6 * C a c ^ 3 * C b d + 18 * C a c ^ 2 * C a d * C b c := by
  have := integral_wick_mul_wick_mul_wick_mul_wick_eq h (List.replicate 3 a) [b]
    (List.replicate 3 c) [d]
  simp only [wickMonomial_singleton] at this
  rw [this]
  simp [taggedLetters, List.finRange_succ, listMatchSum_cons_picks, listMatchSum_nil, picks,
    taggedWeight, List.replicate]
  ring

/-- **(W3)** `E[:X_a^2: :X_b^2: :X_c^2: :X_d^2:]`. -/
theorem integral_wick_two_mul_wick_two_mul_wick_two_mul_wick_two
    (h : IsCentredGaussianVector P X C) (a b c d : Fin n) :
    ∫ ω, wickMonomial C (List.replicate 2 a) (X ω) * wickMonomial C (List.replicate 2 b) (X ω) *
        wickMonomial C (List.replicate 2 c) (X ω) * wickMonomial C (List.replicate 2 d) (X ω) ∂P =
      4 * C a b ^ 2 * C c d ^ 2 + 4 * C a c ^ 2 * C b d ^ 2 + 4 * C a d ^ 2 * C b c ^ 2 +
        16 * (C a b * C a c * C b d * C c d + C a b * C a d * C b c * C c d +
          C a c * C a d * C b c * C b d) := by
  rw [integral_wick_mul_wick_mul_wick_mul_wick_eq h]
  simp [taggedLetters, List.finRange_succ, listMatchSum_cons_picks, listMatchSum_nil, picks,
    taggedWeight, List.replicate]
  ring

/-- **(W4)** `E[:X_a^3: :X_b^2: :X_c^3: :X_d^2:]`. -/
theorem integral_wick_three_mul_wick_two_mul_wick_three_mul_wick_two
    (h : IsCentredGaussianVector P X C) (a b c d : Fin n) :
    ∫ ω, wickMonomial C (List.replicate 3 a) (X ω) * wickMonomial C (List.replicate 2 b) (X ω) *
        wickMonomial C (List.replicate 3 c) (X ω) * wickMonomial C (List.replicate 2 d) (X ω) ∂P =
      36 * C a b ^ 2 * C a c * C c d ^ 2 + 72 * C a b * C a c ^ 2 * C b d * C c d +
        144 * C a b * C a c * C a d * C b c * C c d + 12 * C a c ^ 3 * C b d ^ 2 +
        72 * C a c ^ 2 * C a d * C b c * C b d + 36 * C a c * C a d ^ 2 * C b c ^ 2 := by
  rw [integral_wick_mul_wick_mul_wick_mul_wick_eq h]
  simp [taggedLetters, List.finRange_succ, listMatchSum_cons_picks, listMatchSum_nil, picks,
    taggedWeight, List.replicate]
  ring

end RegularityStructures

end
