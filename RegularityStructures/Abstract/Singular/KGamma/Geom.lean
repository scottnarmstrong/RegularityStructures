/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Two-sided dyadic geometric sums

For `a, b > 0` and every `w > 0`, the sequence `n ↦ min ((2^n w)^a) ((2^n w)^(-b))` is summable
with sum bounded by a constant `C(a, b)` independent of `w`.  This is the elementary estimate
behind the scale splits in the sup bound of `𝒦_γ f` ([Hai14, Prop. 6.16] and Thm. 7.1): the
scales `2^{-n} ≳ w` and `2^{-n} ≲ w` contribute geometric series.
-/

public section

open Filter Finset
open scoped Topology

namespace RegularityStructures.KGammaSup

private theorem rpow_two_pow_nat (j : ℕ) (c : ℝ) :
    ((2 : ℝ) ^ j) ^ c = ((2 : ℝ) ^ c) ^ j := by
  rw [Real.rpow_pow_comm (by norm_num)]

/-- The least `N` with `1 ≤ 2^N w`, with `2^n w < 1` below it. -/
private theorem exists_first_scale {w : ℝ} (hw : 0 < w) :
    ∃ N : ℕ, 1 ≤ (2 : ℝ) ^ N * w ∧ ∀ n < N, (2 : ℝ) ^ n * w < 1 := by
  have h : ∃ N : ℕ, 1 ≤ (2 : ℝ) ^ N * w := by
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (1 / w) (by norm_num : (1 : ℝ) < 2)
    refine ⟨N, ?_⟩
    rw [div_lt_iff₀ hw] at hN
    exact hN.le
  classical
  refine ⟨Nat.find h, Nat.find_spec h, fun n hn => ?_⟩
  exact not_le.1 (Nat.find_min h hn)

private theorem tail_bound {b : ℝ} (hb : 0 < b) {w : ℝ} {N : ℕ} (hN : 1 ≤ (2 : ℝ) ^ N * w)
    (j : ℕ) : ((2 : ℝ) ^ (j + N) * w) ^ (-b) ≤ ((2 : ℝ) ^ (-b)) ^ j := by
  have h1 : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ (j + N) * w := by
    calc (2 : ℝ) ^ j = 2 ^ j * 1 := (mul_one _).symm
      _ ≤ 2 ^ j * (2 ^ N * w) := mul_le_mul_of_nonneg_left hN (by positivity)
      _ = _ := by rw [pow_add]; ring
  have h2 : ((2 : ℝ) ^ (j + N) * w) ^ (-b) ≤ ((2 : ℝ) ^ j) ^ (-b) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith)
  rwa [rpow_two_pow_nat] at h2

private theorem head_sum_bound {a : ℝ} (ha : 0 < a) {w : ℝ} (hw : 0 < w) {N : ℕ}
    (hN : 1 ≤ (2 : ℝ) ^ N * w) (hN' : ∀ n < N, (2 : ℝ) ^ n * w < 1) :
    ∑ n ∈ range N, ((2 : ℝ) ^ n * w) ^ a ≤ 2 ^ a / ((2 : ℝ) ^ a - 1) := by
  have hr : 1 < (2 : ℝ) ^ a := Real.one_lt_rpow (by norm_num) ha
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · simp only [range_zero, sum_empty]
    positivity
  · have hlt : (2 : ℝ) ^ N * w < 2 := by
      have h := hN' (N - 1) (by omega)
      have e : (2 : ℝ) ^ N * w = 2 * ((2 : ℝ) ^ (N - 1) * w) := by
        obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
        simp only [Nat.add_sub_cancel]; ring
      rw [e]; linarith
    have e : ∀ n ∈ range N, ((2 : ℝ) ^ n * w) ^ a = w ^ a * ((2 : ℝ) ^ a) ^ n := by
      intro n _
      rw [Real.mul_rpow (by positivity) hw.le, rpow_two_pow_nat, mul_comm]
    rw [sum_congr rfl e, ← mul_sum, geom_sum_eq hr.ne']
    have hpos : 0 < (2 : ℝ) ^ a - 1 := by linarith
    have h3 : w ^ a * (((2 : ℝ) ^ a) ^ N - 1) / ((2 : ℝ) ^ a - 1) ≤
        ((2 : ℝ) ^ N * w) ^ a / ((2 : ℝ) ^ a - 1) := by
      refine div_le_div_of_nonneg_right ?_ hpos.le
      rw [Real.mul_rpow (by positivity) hw.le, rpow_two_pow_nat, mul_comm]
      nlinarith [Real.rpow_nonneg hw.le a]
    rw [← mul_div_assoc]
    refine h3.trans ?_
    refine div_le_div_of_nonneg_right ?_ hpos.le
    exact (Real.rpow_le_rpow (by positivity) hlt.le ha.le)

/-- **Two-sided dyadic sums.**  If `|u n| ≤ B min ((2^n w)^a) ((2^n w)^(-b))` for all `n`
(`a, b > 0`), then `u` is summable and `|∑ u n| ≤ C B`, where `C` depends only on `a, b`. -/
theorem exists_summable_abs_tsum_le (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : ℝ), 0 < w → ∀ (u : ℕ → ℝ) (B : ℝ), 0 ≤ B →
      (∀ n : ℕ, |u n| ≤ B * min (((2 : ℝ) ^ n * w) ^ a) (((2 : ℝ) ^ n * w) ^ (-b))) →
      Summable u ∧ ∑' n, |u n| ≤ C * B := by
  have hq : (2 : ℝ) ^ (-b) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hq0 : 0 ≤ (2 : ℝ) ^ (-b) := by positivity
  have hra : 1 < (2 : ℝ) ^ a := Real.one_lt_rpow (by norm_num) ha
  refine ⟨2 ^ a / ((2 : ℝ) ^ a - 1) + (1 - (2 : ℝ) ^ (-b))⁻¹, by
    have : 0 < (2 : ℝ) ^ a - 1 := by linarith
    have : 0 < 1 - (2 : ℝ) ^ (-b) := by linarith
    positivity, fun w hw u B hB hu => ?_⟩
  obtain ⟨N, hN, hN'⟩ := exists_first_scale hw
  have hgeom : Summable fun j : ℕ => ((2 : ℝ) ^ (-b)) ^ j := summable_geometric_of_lt_one hq0 hq
  have htail : ∀ j : ℕ, |u (j + N)| ≤ B * ((2 : ℝ) ^ (-b)) ^ j := fun j =>
    (hu (j + N)).trans (mul_le_mul_of_nonneg_left
      ((min_le_right _ _).trans (tail_bound hb hN j)) hB)
  have hsum_tail : Summable fun j : ℕ => |u (j + N)| :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) htail (hgeom.mul_left B)
  have hsum_abs : Summable fun n : ℕ => |u n| := (summable_nat_add_iff N).1 hsum_tail
  refine ⟨hsum_abs.of_abs, ?_⟩
  rw [← hsum_abs.sum_add_tsum_nat_add N]
  have h1 : ∑ n ∈ range N, |u n| ≤ B * (2 ^ a / ((2 : ℝ) ^ a - 1)) := by
    calc ∑ n ∈ range N, |u n| ≤ ∑ n ∈ range N, B * ((2 : ℝ) ^ n * w) ^ a :=
          sum_le_sum fun n _ => (hu n).trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hB)
      _ = B * ∑ n ∈ range N, ((2 : ℝ) ^ n * w) ^ a := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (head_sum_bound ha hw hN hN') hB
  have h2 : ∑' j, |u (j + N)| ≤ B * (1 - (2 : ℝ) ^ (-b))⁻¹ := by
    calc ∑' j, |u (j + N)| ≤ ∑' j : ℕ, B * ((2 : ℝ) ^ (-b)) ^ j :=
          hsum_tail.tsum_le_tsum htail (hgeom.mul_left B)
      _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq]
  calc _ ≤ B * (2 ^ a / ((2 : ℝ) ^ a - 1)) + B * (1 - (2 : ℝ) ^ (-b))⁻¹ := add_le_add h1 h2
    _ = _ := by ring

end RegularityStructures.KGammaSup

end
