/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.Lattice.Count
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Riemann-type sums over lattice boxes

* `sum_rpow_neg_le`: for a finite set `S` of positive integers and `0 ≤ b < 1`,
  `∑_{j ∈ S} j^{-b} ≤ |S|^{1-b} / (1-b)`;
* `sum_latticeBox_fst`: sums over a lattice box of functions of the time index only, and the
  cardinalities of the time and space factors.
-/

public section

open Finset

namespace RegularityStructures.Layer

private theorem sum_range_rpow_neg_le {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) (N : ℕ) :
    ∑ i ∈ range N, (((i + 1 : ℕ) : ℝ)) ^ (-b) ≤ (N : ℝ) ^ (1 - b) / (1 - b) := by
  have hp : 0 < 1 - b := by linarith
  induction N with
  | zero => simp [Real.zero_rpow hp.ne']
  | succ N ih =>
    rw [sum_range_succ]
    have hu : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
    set u : ℝ := ((N + 1 : ℕ) : ℝ) with hu_def
    have hN : (N : ℝ) = u - 1 := by rw [hu_def]; push_cast; ring
    have hs : (-1 : ℝ) ≤ -1 / u := by
      rw [le_div_iff₀ hu, hu_def]; push_cast; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    have hbern := rpow_one_add_le_one_add_mul_self hs hp.le (by linarith : 1 - b ≤ 1)
    have e1 : 1 + -1 / u = (N : ℝ) / u := by rw [hN]; field_simp; ring
    rw [e1, Real.div_rpow (Nat.cast_nonneg N) hu.le] at hbern
    have hup : 0 < u ^ (1 - b) := Real.rpow_pos_of_pos hu _
    have e2 : u ^ (1 - b) / u = u ^ (-b) := by
      rw [← Real.rpow_sub_one hu.ne']; congr 1; ring
    have h3 : (N : ℝ) ^ (1 - b) ≤ u ^ (1 - b) - (1 - b) * u ^ (-b) := by
      rw [div_le_iff₀ hup] at hbern
      have : (1 + (1 - b) * (-1 / u)) * u ^ (1 - b) = u ^ (1 - b) - (1 - b) * (u ^ (1 - b) / u) := by
        ring
      rw [this, e2] at hbern
      exact hbern
    calc ∑ i ∈ range N, (((i + 1 : ℕ) : ℝ)) ^ (-b) + (((N + 1 : ℕ) : ℝ)) ^ (-b)
        ≤ (N : ℝ) ^ (1 - b) / (1 - b) + u ^ (-b) := add_le_add_left ih _
      _ ≤ u ^ (1 - b) / (1 - b) := by
        rw [div_add' _ _ _ hp.ne', div_le_div_iff_of_pos_right hp]
        nlinarith [h3]

/-- `∑_{j ∈ S} j^{-b} ≤ |S|^{1-b}/(1-b)` for a finite set of positive integers. -/
theorem sum_rpow_neg_le {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) (S : Finset ℤ)
    (hS : ∀ j ∈ S, 1 ≤ j) :
    ∑ j ∈ S, ((j : ℤ) : ℝ) ^ (-b) ≤ (S.card : ℝ) ^ (1 - b) / (1 - b) := by
  refine le_trans ?_ (sum_range_rpow_neg_le hb0 hb1 S.card)
  revert hS
  refine Finset.induction_on_max S (by simp) fun a s ha ih hS => ?_
  · have has : a ∉ s := fun h => lt_irrefl _ (ha a h)
    have hs : ∀ j ∈ s, 1 ≤ j := fun j hj => hS j (mem_insert_of_mem hj)
    have ha1 : 1 ≤ a := hS a (mem_insert_self _ _)
    rw [sum_insert has, card_insert_of_notMem has, sum_range_succ]
    have hcard : s.card ≤ (Finset.Icc (1 : ℤ) (a - 1)).card := by
      refine Finset.card_le_card fun j hj => ?_
      rw [Finset.mem_Icc]
      exact ⟨hs j hj, by have := ha j hj; omega⟩
    rw [Int.card_Icc] at hcard
    have hle : ((s.card + 1 : ℕ) : ℝ) ≤ ((a : ℤ) : ℝ) := by
      have : ((s.card + 1 : ℕ) : ℤ) ≤ a := by push_cast; omega
      exact_mod_cast this
    have h1 : ((a : ℤ) : ℝ) ^ (-b) ≤ (((s.card + 1 : ℕ) : ℝ)) ^ (-b) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hle (by linarith)
    linarith [ih hs]

private theorem card_Icc_ceil_floor_le' {x y : ℝ} (h : x ≤ y) :
    ((Finset.Icc ⌈x⌉ ⌊y⌋).card : ℝ) ≤ y - x + 1 := by
  rw [Int.card_Icc]
  by_cases h0 : 0 ≤ ⌊y⌋ + 1 - ⌈x⌉
  · have h2 : (((⌊y⌋ + 1 - ⌈x⌉).toNat : ℕ) : ℝ) = ((⌊y⌋ + 1 - ⌈x⌉ : ℤ) : ℝ) := by
      have : (((⌊y⌋ + 1 - ⌈x⌉).toNat : ℤ) : ℝ) = ((⌊y⌋ + 1 - ⌈x⌉ : ℤ) : ℝ) := by
        rw [Int.toNat_of_nonneg h0]
      exact_mod_cast this
    rw [h2]
    push_cast
    linarith [Int.floor_le y, Int.le_ceil x]
  · rw [Int.toNat_of_nonpos (not_le.1 h0).le]
    simp
    linarith

theorem card_latticeBox_time_le (n : ℕ) (x : ParabolicSpace) {rt : ℝ} (hrt : 0 ≤ rt) :
    ((Finset.Icc ⌈(4 : ℝ) ^ n * (x.1 - rt)⌉ ⌊(4 : ℝ) ^ n * (x.1 + rt)⌋).card : ℝ) ≤
      2 * 4 ^ n * rt + 2 := by
  have h4 : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
  have := card_Icc_ceil_floor_le' (x := (4 : ℝ) ^ n * (x.1 - rt))
    (y := (4 : ℝ) ^ n * (x.1 + rt)) (by nlinarith)
  nlinarith

theorem card_latticeBox_space_le (n : ℕ) (x : ParabolicSpace) {rs : ℝ} (hrs : 0 ≤ rs) :
    ((Fintype.piFinset fun i : Fin 3 =>
      Finset.Icc ⌈(2 : ℝ) ^ n * (x.2 i - rs)⌉ ⌊(2 : ℝ) ^ n * (x.2 i + rs)⌋).card : ℝ) ≤
      (2 * 2 ^ n * rs + 2) ^ 3 := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hB : ∀ i : Fin 3,
      ((Finset.Icc ⌈(2 : ℝ) ^ n * (x.2 i - rs)⌉ ⌊(2 : ℝ) ^ n * (x.2 i + rs)⌋).card : ℝ) ≤
      2 * 2 ^ n * rs + 2 := fun i => by
    have := card_Icc_ceil_floor_le' (x := (2 : ℝ) ^ n * (x.2 i - rs))
      (y := (2 : ℝ) ^ n * (x.2 i + rs)) (by nlinarith)
    nlinarith
  rw [Fintype.card_piFinset]
  push_cast
  calc (∏ i : Fin 3, ((Finset.Icc ⌈(2 : ℝ) ^ n * (x.2 i - rs)⌉
        ⌊(2 : ℝ) ^ n * (x.2 i + rs)⌋).card : ℝ))
      ≤ ∏ _i : Fin 3, (2 * 2 ^ n * rs + 2) :=
        Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => hB i
    _ = (2 * 2 ^ n * rs + 2) ^ 3 := by simp

/-- Sum over a lattice box of a function of the time index only. -/
theorem sum_latticeBox_fst (n : ℕ) (x : ParabolicSpace) (rt rs : ℝ) (F : ℤ → ℝ) :
    ∑ k ∈ latticeBox n x rt rs, F k.1 =
      ((Fintype.piFinset fun i : Fin 3 =>
        Finset.Icc ⌈(2 : ℝ) ^ n * (x.2 i - rs)⌉ ⌊(2 : ℝ) ^ n * (x.2 i + rs)⌋).card : ℝ) *
      ∑ j ∈ Finset.Icc ⌈(4 : ℝ) ^ n * (x.1 - rt)⌉ ⌊(4 : ℝ) ^ n * (x.1 + rt)⌋, F j := by
  unfold latticeBox
  rw [Finset.sum_product]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.mul_sum]

end RegularityStructures.Layer

end
