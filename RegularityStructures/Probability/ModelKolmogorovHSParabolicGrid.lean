/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.KolmogorovChentsovFinite
public import RegularityStructures.Analysis.Parabolic.Basic

/-!
# Parabolic dyadic grids for the model Kolmogorov criterion

The covering argument of Hairer--Steele, arXiv:2301.10081v3, Proposition B.3,
uses the scaling dimension rather than the topological dimension. On the unit
space-time box the time mesh is `2^(-2n)` and the three spatial meshes are
`2^(-n)`. Thus the grid has at most `16 * 2^(5n)` points.

These grids are deterministic geometry, independent of any random-model or
pathwise-bound hypothesis.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- Indices of the anisotropic dyadic grid in the unit space-time box. -/
abbrev HSParabolicGridIndex (n : ℕ) :=
  Fin (2 ^ (2 * n) + 1) × (Fin 3 → Fin (2 ^ n + 1))

/-- Exactly one time coordinate at level `2n` and three spatial coordinates at level `n`. -/
theorem card_hsParabolicGridIndex (n : ℕ) :
    Fintype.card (HSParabolicGridIndex n) = (2 ^ (2 * n) + 1) * (2 ^ n + 1) ^ 3 := by
  simp [HSParabolicGridIndex]

/-- The grid has parabolic dimension five. -/
theorem card_hsParabolicGridIndex_le (n : ℕ) :
    Fintype.card (HSParabolicGridIndex n) ≤ 16 * 2 ^ (5 * n) := by
  rw [card_hsParabolicGridIndex]
  have h (k : ℕ) : 2 ^ k + 1 ≤ 2 * 2 ^ k := by
    have : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
    omega
  calc
    (2 ^ (2 * n) + 1) * (2 ^ n + 1) ^ 3 ≤
        (2 * 2 ^ (2 * n)) * (2 * 2 ^ n) ^ 3 :=
      Nat.mul_le_mul (h _) (Nat.pow_le_pow_left (h _) _)
    _ = 16 * 2 ^ (5 * n) := by
      rw [show 5 * n = 2 * n + n * 3 by omega, pow_add, pow_mul]
      ring

end RegularityStructures

end
