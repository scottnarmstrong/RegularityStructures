/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovHSCompactNet

/-!
# Cell representatives at the dyadic mesh

A point `x ∈ S` of a subset of the unit box lies within parabolic distance `4 · 2^{-N}` of the
representative of its own occupied cell.
-/

public section

namespace RegularityStructures

theorem parabolicNorm_sub_cellRepresentative_le (S : Set ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ j, x.2 j ∈ Set.Icc (0 : ℝ) 1)
    (N : ℕ) {x : ParabolicSpace} (hx : x ∈ S) :
    parabolicNorm (x - (hsParabolicCellApprox S N ⟨x, hx⟩ : ParabolicSpace)) ≤
      4 * (2 : ℝ) ^ (-(N : ℤ)) := by
  rw [parabolicNorm_sub_comm, zpow_neg, zpow_natCast, ← div_eq_mul_inv]
  exact hsParabolicCellApprox_error_le S hbox N ⟨x, hx⟩

end RegularityStructures

end
