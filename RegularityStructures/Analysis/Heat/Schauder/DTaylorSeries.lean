/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.TaylorSeries
public import RegularityStructures.Analysis.Heat.Schauder.Holder
public import RegularityStructures.Analysis.Heat.Schauder.TaylorDyadicSum

/-!
# A two-sided geometric summation lemma

`series_core`: if `U : ℕ → ℝ` is summable, `|U n| ≤ ∑_j u_j 2^{δ_j n}` for `n < m` (growth,
`δ_j > 0`) and `|U n| ≤ ∑_j v_j 2^{-ε_j n}` for `n ≥ m` (decay, `ε_j > 0`), where `m` is the first
index with `d 2^m > 1`, then `|∑' U| ≤ ∑_j u_j (2/d)^{δ_j}/(2^{δ_j} - 1) + ∑_j v_j d^{ε_j}/(1 - 2^{-ε_j})`.
This is the summation pattern of [Hai14, proof of Theorem 5.12] (large scales `2^{-n} ≥ d`, small
scales `2^{-n} < d`).
-/

public section

namespace RegularityStructures

theorem series_core {ι₁ ι₂ : Type*} (s₁ : Finset ι₁) (s₂ : Finset ι₂) {u : ι₁ → ℝ} {v : ι₂ → ℝ}
    {δ : ι₁ → ℝ} {ε : ι₂ → ℝ} (hu : ∀ j ∈ s₁, 0 ≤ u j) (hv : ∀ j ∈ s₂, 0 ≤ v j)
    (hδ : ∀ j ∈ s₁, 0 < δ j) (hε : ∀ j ∈ s₂, 0 < ε j) {d : ℝ} (hd : 0 < d) {m : ℕ}
    (hm2 : ∀ n, m ≤ n → 1 < d * 2 ^ n) (hm3 : m = 0 ∨ d * 2 ^ m ≤ 2) {U : ℕ → ℝ}
    (hU : Summable U)
    (hL : ∀ n < m, |U n| ≤ ∑ j ∈ s₁, u j * (2 : ℝ) ^ (δ j * n))
    (hS : ∀ n, m ≤ n → |U n| ≤ ∑ j ∈ s₂, v j * (2 : ℝ) ^ (-ε j * n)) :
    |∑' n, U n| ≤ (∑ j ∈ s₁, u j * (((2 : ℝ) / d) ^ δ j / ((2 : ℝ) ^ δ j - 1))) +
      ∑ j ∈ s₂, v j * (d ^ ε j / (1 - (2 : ℝ) ^ (-ε j))) := by
  have hsplit := hU.sum_add_tsum_nat_add m
  rw [← hsplit]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · -- head
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ n ∈ Finset.range m, |U n|
        ≤ ∑ n ∈ Finset.range m, ∑ j ∈ s₁, u j * ((2 : ℝ) ^ δ j) ^ n := by
          refine Finset.sum_le_sum fun n hn => (hL n (Finset.mem_range.1 hn)).trans (le_of_eq ?_)
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Real.rpow_mul_natCast (by norm_num)]
      _ = ∑ j ∈ s₁, u j * ∑ n ∈ Finset.range m, ((2 : ℝ) ^ δ j) ^ n := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm
      _ ≤ _ := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hρ : 1 < (2 : ℝ) ^ δ j := Real.one_lt_rpow (by norm_num) (hδ j hj)
          have hρ0 : 0 < (2 : ℝ) ^ δ j - 1 := by linarith
          refine mul_le_mul_of_nonneg_left ?_ (hu j hj)
          rcases hm3 with rfl | hm
          · simp only [Finset.range_zero, Finset.sum_empty]
            exact div_nonneg (Real.rpow_nonneg (div_nonneg (by norm_num) hd.le) _) hρ0.le
          · have h1 : ((2 : ℝ) ^ δ j) ^ m ≤ (2 / d) ^ δ j := by
              rw [two_rpow_pow_eq]
              refine Real.rpow_le_rpow (by positivity) ?_ (hδ j hj).le
              rw [le_div_iff₀ hd]; linarith
            exact (sum_range_geom_le hρ m).trans (div_le_div_of_nonneg_right h1 hρ0.le)
  · -- tail
    have hg : ∀ j ∈ s₂, HasSum (fun n : ℕ => v j * ((2 : ℝ) ^ (-ε j)) ^ (n + m))
        (v j * ((2 : ℝ) ^ (-ε j)) ^ m / (1 - (2 : ℝ) ^ (-ε j))) := by
      intro j hj
      have hr : (2 : ℝ) ^ (-ε j) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith [hε j hj])
      have := (hasSum_geometric_of_lt_one (Real.rpow_nonneg (by norm_num) _) hr).mul_left
        (v j * ((2 : ℝ) ^ (-ε j)) ^ m)
      have e : (fun n : ℕ => v j * ((2 : ℝ) ^ (-ε j)) ^ (n + m)) =
          fun i : ℕ => v j * ((2 : ℝ) ^ (-ε j)) ^ m * ((2 : ℝ) ^ (-ε j)) ^ i := by
        funext n; rw [pow_add]; ring
      rw [e, div_eq_mul_inv]
      exact this
    have hsum := hasSum_sum hg
    have hb := tsum_of_norm_bounded hsum (f := fun n => U (n + m)) fun n => by
      rw [Real.norm_eq_abs]
      refine (hS (n + m) (Nat.le_add_left m n)).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Real.rpow_mul_natCast (by norm_num)]
    rw [Real.norm_eq_abs] at hb
    refine hb.trans ?_
    refine Finset.sum_le_sum fun j hj => ?_
    have hr : (2 : ℝ) ^ (-ε j) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith [hε j hj])
    have h1 := rpow_two_pow_le (hε j hj) hd (hm2 m le_rfl)
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h1 (by linarith)) (hv j hj)

theorem sum_range_list_comm {α : Type*} (L : List α) (g : α → ℕ → ℝ) (m : ℕ) :
    ∑ n ∈ Finset.range m, (L.map fun p => g p n).sum =
      (L.map fun p => ∑ n ∈ Finset.range m, g p n).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

theorem series_core_list (L₁ L₂ : List (ℝ × ℝ)) (hu : ∀ p ∈ L₁, 0 ≤ p.1 ∧ 0 < p.2)
    (hv : ∀ p ∈ L₂, 0 ≤ p.1 ∧ 0 < p.2) {d : ℝ} (hd : 0 < d) {m : ℕ}
    (hm2 : ∀ n, m ≤ n → 1 < d * 2 ^ n) (hm3 : m = 0 ∨ d * 2 ^ m ≤ 2) {U : ℕ → ℝ}
    (hU : Summable U)
    (hL : ∀ n < m, |U n| ≤ (L₁.map fun p => p.1 * (2 : ℝ) ^ (p.2 * (n : ℝ))).sum)
    (hS : ∀ n, m ≤ n → |U n| ≤ (L₂.map fun p => p.1 * (2 : ℝ) ^ (-p.2 * (n : ℝ))).sum) :
    |∑' n, U n| ≤ (L₁.map fun p => p.1 * (((2 : ℝ) / d) ^ p.2 / ((2 : ℝ) ^ p.2 - 1))).sum +
      (L₂.map fun p => p.1 * (d ^ p.2 / (1 - (2 : ℝ) ^ (-p.2)))).sum := by
  have hsplit := hU.sum_add_tsum_nat_add m
  rw [← hsplit]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ n ∈ Finset.range m, |U n|
        ≤ ∑ n ∈ Finset.range m, (L₁.map fun p => p.1 * ((2 : ℝ) ^ p.2) ^ n).sum := by
          refine Finset.sum_le_sum fun n hn => (hL n (Finset.mem_range.1 hn)).trans (le_of_eq ?_)
          congr 1
          refine List.map_congr_left fun p _ => ?_
          rw [Real.rpow_mul_natCast (by norm_num)]
      _ = (L₁.map fun p => p.1 * ∑ n ∈ Finset.range m, ((2 : ℝ) ^ p.2) ^ n).sum := by
          rw [sum_range_list_comm L₁ (fun p n => p.1 * ((2 : ℝ) ^ p.2) ^ n) m]
          congr 1
          refine List.map_congr_left fun p _ => ?_
          rw [Finset.mul_sum]
      _ ≤ _ := by
          refine List.sum_le_sum fun p hp => ?_
          obtain ⟨hp1, hp2⟩ := hu p hp
          have hρ : 1 < (2 : ℝ) ^ p.2 := Real.one_lt_rpow (by norm_num) hp2
          have hρ0 : 0 < (2 : ℝ) ^ p.2 - 1 := by linarith
          refine mul_le_mul_of_nonneg_left ?_ hp1
          rcases hm3 with rfl | hm
          · simp only [Finset.range_zero, Finset.sum_empty]
            exact div_nonneg (Real.rpow_nonneg (div_nonneg (by norm_num) hd.le) _) hρ0.le
          · have h1 : ((2 : ℝ) ^ p.2) ^ m ≤ (2 / d) ^ p.2 := by
              rw [two_rpow_pow_eq]
              refine Real.rpow_le_rpow (by positivity) ?_ hp2.le
              rw [le_div_iff₀ hd]; linarith
            exact (sum_range_geom_le hρ m).trans (div_le_div_of_nonneg_right h1 hρ0.le)
  · have hg : ∀ p ∈ L₂, HasSum (fun n : ℕ => p.1 * ((2 : ℝ) ^ (-p.2)) ^ (n + m))
        (p.1 * ((2 : ℝ) ^ (-p.2)) ^ m / (1 - (2 : ℝ) ^ (-p.2))) := by
      intro p hp
      have hr : (2 : ℝ) ^ (-p.2) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith [(hv p hp).2])
      have := (hasSum_geometric_of_lt_one (Real.rpow_nonneg (by norm_num) _) hr).mul_left
        (p.1 * ((2 : ℝ) ^ (-p.2)) ^ m)
      have e : (fun n : ℕ => p.1 * ((2 : ℝ) ^ (-p.2)) ^ (n + m)) =
          fun i : ℕ => p.1 * ((2 : ℝ) ^ (-p.2)) ^ m * ((2 : ℝ) ^ (-p.2)) ^ i := by
        funext n; rw [pow_add]; ring
      rw [e, div_eq_mul_inv]
      exact this
    have hsum := hasSum_list_sum L₂ (fun p n => p.1 * ((2 : ℝ) ^ (-p.2)) ^ (n + m)) _ hg
    have hb := tsum_of_norm_bounded hsum (f := fun n => U (n + m)) fun n => by
      rw [Real.norm_eq_abs]
      refine (hS (n + m) (Nat.le_add_left m n)).trans (le_of_eq ?_)
      congr 1
      refine List.map_congr_left fun p _ => ?_
      rw [← Real.rpow_mul_natCast (by norm_num)]
    rw [Real.norm_eq_abs] at hb
    refine hb.trans ?_
    refine List.sum_le_sum fun p hp => ?_
    have hr : (2 : ℝ) ^ (-p.2) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith [(hv p hp).2])
    have h1 := rpow_two_pow_le (hv p hp).2 hd (hm2 m le_rfl)
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h1 (by linarith)) (hv p hp).1

/-- `series_core_list` with the powers of `d` split off: pairs `(A, a, δ)` stand for the terms
`A d^a 2^{δ n}` (growth) and `A d^a 2^{-δ n}` (decay), with `a - δ = σ` resp. `a + δ = σ`. -/
theorem series_core_triple (L₁ L₂ : List (ℝ × ℝ × ℝ)) (σ : ℝ)
    (hu : ∀ p ∈ L₁, 0 ≤ p.1 ∧ 0 < p.2.2 ∧ p.2.1 - p.2.2 = σ)
    (hv : ∀ p ∈ L₂, 0 ≤ p.1 ∧ 0 < p.2.2 ∧ p.2.1 + p.2.2 = σ) {d : ℝ} (hd : 0 < d) {m : ℕ}
    (hm2 : ∀ n, m ≤ n → 1 < d * 2 ^ n) (hm3 : m = 0 ∨ d * 2 ^ m ≤ 2) {U : ℕ → ℝ}
    (hU : Summable U)
    (hL : ∀ n < m, |U n| ≤
      (L₁.map fun p => p.1 * d ^ p.2.1 * (2 : ℝ) ^ (p.2.2 * (n : ℝ))).sum)
    (hS : ∀ n, m ≤ n → |U n| ≤
      (L₂.map fun p => p.1 * d ^ p.2.1 * (2 : ℝ) ^ (-p.2.2 * (n : ℝ))).sum) :
    |∑' n, U n| ≤ ((L₁.map fun p => p.1 * ((2 : ℝ) ^ p.2.2 / ((2 : ℝ) ^ p.2.2 - 1))).sum +
      (L₂.map fun p => p.1 / (1 - (2 : ℝ) ^ (-p.2.2))).sum) * d ^ σ := by
  have h := series_core_list (L₁.map fun p => (p.1 * d ^ p.2.1, p.2.2))
    (L₂.map fun p => (p.1 * d ^ p.2.1, p.2.2)) (fun q hq => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
      obtain ⟨h1, h2, -⟩ := hu p hp
      exact ⟨mul_nonneg h1 (Real.rpow_nonneg hd.le _), h2⟩) (fun q hq => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
      obtain ⟨h1, h2, -⟩ := hv p hp
      exact ⟨mul_nonneg h1 (Real.rpow_nonneg hd.le _), h2⟩) hd hm2 hm3 hU
    (fun n hn => by rw [List.map_map]; exact hL n hn)
    (fun n hn => by rw [List.map_map]; exact hS n hn)
  simp only [List.map_map] at h
  refine h.trans (le_of_eq ?_)
  rw [add_mul, ← List.sum_map_mul_right, ← List.sum_map_mul_right]
  congr 1
  · congr 1
    refine List.map_congr_left fun p hp => ?_
    obtain ⟨-, h2, h3⟩ := hu p hp
    have : d ^ p.2.1 * (2 / d) ^ p.2.2 = (2 : ℝ) ^ p.2.2 * d ^ σ := by
      rw [Real.div_rpow (by norm_num) hd.le, ← h3, Real.rpow_sub hd]
      field_simp
    calc p.1 * d ^ p.2.1 * ((2 / d) ^ p.2.2 / ((2 : ℝ) ^ p.2.2 - 1))
        = p.1 * (d ^ p.2.1 * (2 / d) ^ p.2.2) / ((2 : ℝ) ^ p.2.2 - 1) := by ring
      _ = _ := by rw [this]; ring
  · congr 1
    refine List.map_congr_left fun p hp => ?_
    obtain ⟨-, h2, h3⟩ := hv p hp
    have : d ^ p.2.1 * d ^ p.2.2 = d ^ σ := by rw [← Real.rpow_add hd, h3]
    calc p.1 * d ^ p.2.1 * (d ^ p.2.2 / (1 - (2 : ℝ) ^ (-p.2.2)))
        = p.1 * (d ^ p.2.1 * d ^ p.2.2) / (1 - (2 : ℝ) ^ (-p.2.2)) := by ring
      _ = _ := by rw [this]; ring

end RegularityStructures

end
