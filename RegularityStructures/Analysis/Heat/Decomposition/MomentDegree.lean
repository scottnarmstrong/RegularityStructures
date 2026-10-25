/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Decomposition.Moment
public import RegularityStructures.Analysis.Heat.Decomposition.Vanishing
public import RegularityStructures.Analysis.Heat.Decomposition.VanishingLineIter

/-!
# Scaled degrees

Two elementary facts on scaled degrees: monotonicity of `multiDeg` (`multiDeg_le_of_le`) and
`rpow_neg_two_mul_nat`.
-/

public section

open MeasureTheory
open scoped ContDiff

namespace RegularityStructures

theorem multiDeg_le_of_le {k l : Fin 4 →₀ ℕ} (h : k ≤ l) : multiDeg k ≤ multiDeg l := by
  unfold multiDeg
  rw [weight_parabolicWeight, weight_parabolicWeight]
  have := h 0
  have := h 1
  have := h 2
  have := h 3
  omega

theorem rpow_neg_two_mul_nat (n : ℕ) :
    (2 : ℝ) ^ (-(2 : ℝ) * (n : ℝ)) = (((2 : ℝ) ^ n) ^ 2)⁻¹ := by
  have : -(2 : ℝ) * (n : ℝ) = -((2 * n : ℕ) : ℝ) := by push_cast; ring
  rw [this, Real.rpow_neg (by norm_num), Real.rpow_natCast, pow_mul']

end RegularityStructures

end
