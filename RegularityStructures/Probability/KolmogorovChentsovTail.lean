/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.KolmogorovChentsovSupremum
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Geometric dyadic tails

The approximation telescope has a geometric tail.  This file keeps the
calculation in `ℝ≥0∞`, including the case where no integrability assumption on
the original process is available.
-/

@[expose] public section

open scoped ENNReal NNReal Topology

namespace RegularityStructures

theorem dyadicBase_tail_rpow_sum {r : ℝ≥0} (hr : 0 < r) (n : ℕ) :
    ∑' k : ℕ, (dyadicBase (n + k + 1)) ^ (r : ℝ) =
      (dyadicBase n) ^ (r : ℝ) *
        (((2 : ℝ≥0∞)⁻¹) ^ (r : ℝ) *
          (1 - ((2 : ℝ≥0∞)⁻¹) ^ (r : ℝ))⁻¹) := by
  let a : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹
  let b : ℝ≥0∞ := a ^ (r : ℝ)
  have hb : b < 1 := by
    dsimp [b, a]
    exact ENNReal.rpow_lt_one (by norm_num) hr
  have hterm : ∀ k : ℕ,
      (dyadicBase (n + k + 1)) ^ (r : ℝ) =
        (dyadicBase n) ^ (r : ℝ) * (b * b ^ k) := by
    intro k
    have hbase : dyadicBase (n + k + 1) =
        dyadicBase n * dyadicBase (k + 1) := by
      simp [dyadicBase, pow_add, Nat.add_assoc]
    calc
      (dyadicBase (n + k + 1)) ^ (r : ℝ) =
          (dyadicBase n * dyadicBase (k + 1)) ^ (r : ℝ) := by rw [hbase]
      _ = (dyadicBase n) ^ (r : ℝ) *
          (dyadicBase (k + 1)) ^ (r : ℝ) :=
        ENNReal.mul_rpow_of_nonneg _ _ hr.le
      _ = (dyadicBase n) ^ (r : ℝ) * b ^ (k + 1) := by
        have hk1 := dyadicBase_rpow_eq_geometric (γ := (r : ℝ)) (k + 1)
        simpa [a, b] using congrArg (fun z : ℝ≥0∞ =>
          (dyadicBase n) ^ (r : ℝ) * z) hk1
      _ = (dyadicBase n) ^ (r : ℝ) * (b * b ^ k) := by
        rw [pow_succ]
        ac_rfl
  rw [show (fun k : ℕ => (dyadicBase (n + k + 1)) ^ (r : ℝ)) =
      (fun k : ℕ => (dyadicBase n) ^ (r : ℝ) * (b * b ^ k)) by
        funext k; exact hterm k]
  rw [ENNReal.tsum_mul_left]
  rw [show (∑' k : ℕ, b * b ^ k) = b * ∑' k : ℕ, b ^ k by
    rw [ENNReal.tsum_mul_left]]
  rw [ENNReal.tsum_geometric]

end RegularityStructures

end
