/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Sequences with geometrically decaying increments; the first dyadic level

* `exists_tendsto_of_geometric_increments`: if `|a (n₀ + j + 1) - a (n₀ + j)| ≤ D r^j`, `r < 1`,
  then `a` converges, with `|lim - a n₀| ≤ D / (1 - r)`.
* `exists_level_eight_mul_inv_le`: for `0 < λ ≤ 1` there is a dyadic level `n` with
  `8 · 2^{-n} ≤ λ ≤ 16 · 2^{-n}`.
-/

public section

open Filter
open scoped Topology

namespace RegularityStructures

theorem exists_tendsto_of_geometric_increments (a : ℕ → ℝ) (n₀ : ℕ) {D r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) (h : ∀ j, |a (n₀ + j + 1) - a (n₀ + j)| ≤ D * r ^ j) :
    ∃ L, Tendsto a atTop (𝓝 L) ∧ |L - a n₀| ≤ D / (1 - r) := by
  set g : ℕ → ℝ := fun j => a (j + n₀) with hg
  have hd : ∀ j, dist (g j) (g j.succ) ≤ D * r ^ j := fun j => by
    rw [Real.dist_eq, abs_sub_comm]
    have := h j
    rw [add_comm n₀ j] at this
    simpa [hg, Nat.succ_eq_add_one, add_assoc, add_comm, add_left_comm] using this
  have hs : Summable fun j : ℕ => D * r ^ j := (summable_geometric_of_lt_one hr0 hr1).mul_left D
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_dist_le_of_summable _ hd hs)
  refine ⟨L, (tendsto_add_atTop_iff_nat n₀).1 hL, ?_⟩
  have := dist_le_tsum_of_dist_le_of_tendsto₀ _ hd hs hL
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, Real.dist_eq] at this
  rw [abs_sub_comm]
  simpa [hg, div_eq_mul_inv] using this

theorem exists_level_eight_mul_inv_le {lam : ℝ} (hlam : 0 < lam) (hl1 : lam ≤ 1) :
    ∃ n : ℕ, 8 * ((2 : ℝ) ^ n)⁻¹ ≤ lam ∧ lam ≤ 16 * ((2 : ℝ) ^ n)⁻¹ := by
  classical
  have hex : ∃ n : ℕ, 8 * ((2 : ℝ) ^ n)⁻¹ ≤ lam := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (8 / lam) (by norm_num : (1 : ℝ) < 2)
    refine ⟨n, ?_⟩
    have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    rw [div_lt_iff₀ hlam] at hn
    rw [← div_eq_mul_inv, div_le_iff₀ h2]
    linarith
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  have h0 : Nat.find hex ≠ 0 := by
    intro h
    have := Nat.find_spec hex
    rw [h] at this
    norm_num at this
    linarith
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero h0
  have hmin := Nat.find_min hex (show m < Nat.find hex by omega)
  push Not at hmin
  rw [hm, pow_succ]
  have h2 : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have e : 16 * ((2 : ℝ) ^ m * 2)⁻¹ = 8 * ((2 : ℝ) ^ m)⁻¹ := by field_simp; norm_num
  rw [e]
  exact hmin.le

end RegularityStructures

end
