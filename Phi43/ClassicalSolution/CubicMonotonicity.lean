/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.ClassicalSolution

/-!
# The cubic monotonicity input for uniqueness

The pointwise algebraic inequality below is the sign input in the usual `L²` energy proof of
uniqueness for the regularised dynamical Φ⁴₃ equation. It is recorded independently of the
integration-by-parts and periodic-lift infrastructure that would be needed for the full W4 result.
-/

public section

namespace RegularityStructures.Phi43

theorem cubic_difference_mul_nonneg (a b : ℝ) :
    0 ≤ (a ^ 3 - b ^ 3) * (a - b) := by
  have hquad : 0 ≤ a ^ 2 + a * b + b ^ 2 := by
    nlinarith [sq_nonneg (a + b), sq_nonneg a, sq_nonneg b]
  rw [show (a ^ 3 - b ^ 3) * (a - b) =
      (a - b) ^ 2 * (a ^ 2 + a * b + b ^ 2) by ring]
  exact mul_nonneg (sq_nonneg _) hquad

end RegularityStructures.Phi43

end
