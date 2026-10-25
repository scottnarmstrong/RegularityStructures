/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Sequences with geometrically bounded increments

If `|a (j+1) - a j| ≤ A₁ q₁^j + A₂ q₂^j` with `0 ≤ q₁, q₂ < 1` then `a` converges to a limit `L`
with `|L - a 0| ≤ A₁ / (1 - q₁) + A₂ / (1 - q₂)`.
-/

public section

open Filter Topology

namespace RegularityStructures.Layer

theorem exists_tendsto_of_abs_sub_le {a : ℕ → ℝ} {A₁ A₂ q₁ q₂ : ℝ}
    (hq₁ : 0 ≤ q₁) (hq₁' : q₁ < 1) (hq₂ : 0 ≤ q₂) (hq₂' : q₂ < 1)
    (h : ∀ j, |a (j + 1) - a j| ≤ A₁ * q₁ ^ j + A₂ * q₂ ^ j) :
    ∃ L, Tendsto a atTop (𝓝 L) ∧ |L - a 0| ≤ A₁ / (1 - q₁) + A₂ / (1 - q₂) := by
  set B : ℕ → ℝ := fun j => A₁ * q₁ ^ j + A₂ * q₂ ^ j with hB
  have hs1 : Summable fun j : ℕ => A₁ * q₁ ^ j :=
    (summable_geometric_of_lt_one hq₁ hq₁').mul_left _
  have hs2 : Summable fun j : ℕ => A₂ * q₂ ^ j :=
    (summable_geometric_of_lt_one hq₂ hq₂').mul_left _
  have hsB : Summable B := hs1.add hs2
  have hcau : CauchySeq a := by
    refine cauchySeq_of_summable_dist ?_
    refine Summable.of_nonneg_of_le (fun j => dist_nonneg) (fun j => ?_) hsB
    rw [Real.dist_eq, abs_sub_comm]
    exact h j
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcau
  refine ⟨L, hL, ?_⟩
  have htsum : ∑' j, B j = A₁ / (1 - q₁) + A₂ / (1 - q₂) := by
    rw [hB, hs1.tsum_add hs2, tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one hq₁ hq₁',
      tsum_geometric_of_lt_one hq₂ hq₂', div_eq_mul_inv, div_eq_mul_inv]
  rw [← htsum]
  have hb : ∀ N, |a N - a 0| ≤ ∑' j, B j := by
    intro N
    have := dist_le_range_sum_dist a N
    rw [Real.dist_eq, abs_sub_comm] at this
    refine this.trans ?_
    refine le_trans (Finset.sum_le_sum fun j _ => ?_) (hsB.sum_le_tsum (Finset.range N)
      (fun j _ => (abs_nonneg _).trans (h j)))
    rw [Real.dist_eq, abs_sub_comm]
    exact h j
  exact le_of_tendsto' ((hL.sub_const (a 0)).abs) hb

end RegularityStructures.Layer

end
