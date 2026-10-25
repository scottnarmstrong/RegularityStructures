/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.Index

/-!
# Geometric pieces for the dyadic summation

`headSeq u ρ m n = u ρ^n` for `n < m` (zero otherwise) and `tailSeq u r m n = u r^n` for `n ≥ m`.
With `m` the first index with `d 2^m > 1`:

* `sum_range_geom_le`: `∑_{n<m} ρ^n ≤ (2/d)^δ/(ρ - 1)` for `ρ = 2^δ > 1`;
* `hasSum_tailSeq`, `rpow_two_pow_le`: `∑_{n ≥ m} r^n ≤ d^ε/(1 - r)` for `r = 2^{-ε} < 1`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- `n ↦ u ρ^n` for `n < m`, `0` for `n ≥ m`. -/
def headSeq (u ρ : ℝ) (m : ℕ) (n : ℕ) : ℝ := if n < m then u * ρ ^ n else 0

/-- `n ↦ u r^n` for `n ≥ m`, `0` for `n < m`. -/
def tailSeq (u r : ℝ) (m : ℕ) (n : ℕ) : ℝ := if m ≤ n then u * r ^ n else 0

end RegularityStructures

end

public section

namespace RegularityStructures

theorem hasSum_headSeq (u ρ : ℝ) (m : ℕ) :
    HasSum (headSeq u ρ m) (∑ n ∈ Finset.range m, u * ρ ^ n) := by
  have h : HasSum (headSeq u ρ m) (∑ n ∈ Finset.range m, headSeq u ρ m n) :=
    hasSum_sum_of_ne_finset_zero (fun n hn => by
      have : ¬ n < m := fun h => hn (Finset.mem_range.2 h)
      simp [headSeq, this])
  convert h using 1
  refine Finset.sum_congr rfl fun n hn => ?_
  simp [headSeq, Finset.mem_range.1 hn]

theorem hasSum_tailSeq {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (u : ℝ) (m : ℕ) :
    HasSum (tailSeq u r m) (u * r ^ m / (1 - r)) := by
  rw [← hasSum_nat_add_iff' m]
  have h0 : ∑ i ∈ Finset.range m, tailSeq u r m i = 0 :=
    Finset.sum_eq_zero fun i hi => by
      have : ¬ m ≤ i := not_le.2 (Finset.mem_range.1 hi)
      simp [tailSeq, this]
  rw [h0, sub_zero]
  have := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (u * r ^ m)
  convert this using 1
  · funext n; simp [tailSeq, pow_add]; ring
  · field_simp

theorem sum_range_geom_le {ρ : ℝ} (hρ : 1 < ρ) (m : ℕ) : ∑ n ∈ Finset.range m, ρ ^ n ≤ ρ ^ m / (ρ - 1) := by
  rw [geom_sum_eq hρ.ne']
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

theorem rpow_two_pow_le {ε d : ℝ} (hε : 0 < ε) (hd : 0 < d) {m : ℕ} (hm : 1 < d * 2 ^ m) :
    ((2 : ℝ) ^ (-ε)) ^ m ≤ d ^ ε := by
  have h2 : (0 : ℝ) < 2 ^ m := by positivity
  have hdm : d⁻¹ ≤ 2 ^ m := by
    rw [inv_le_comm₀ hd h2, inv_eq_one_div, div_le_iff₀ h2]
    linarith
  rw [two_rpow_pow_eq]
  calc ((2 : ℝ) ^ m) ^ (-ε) ≤ (d⁻¹) ^ (-ε) := Real.rpow_le_rpow_of_nonpos (by positivity) hdm (by linarith)
    _ = d ^ ε := by rw [Real.inv_rpow hd.le, Real.rpow_neg hd.le, inv_inv]

theorem exists_splitIndex' {d : ℝ} (hd : 0 < d) :
    ∃ m : ℕ, (∀ n < m, d * 2 ^ n ≤ 1) ∧ (∀ n, m ≤ n → 1 < d * 2 ^ n) ∧
      (m = 0 ∨ d * 2 ^ m ≤ 2) := by
  classical
  have hex : ∃ m : ℕ, 1 < d * 2 ^ m := by
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (1 / d) (by norm_num : (1 : ℝ) < 2)
    refine ⟨m, ?_⟩
    rw [div_lt_iff₀ hd] at hm
    linarith
  refine ⟨Nat.find hex, fun n hn => not_lt.1 (Nat.find_min hex hn), fun n hn => ?_, ?_⟩
  · have h1 := Nat.find_spec hex
    calc (1 : ℝ) < d * 2 ^ Nat.find hex := h1
      _ ≤ d * 2 ^ n := mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ (by norm_num) hn) hd.le
  · by_cases h0 : Nat.find hex = 0
    · exact Or.inl h0
    · right
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h0
      have := not_lt.1 (Nat.find_min hex (show k < Nat.find hex by omega))
      rw [hk, pow_succ]
      linarith

theorem head_piece_le {d u : ℝ} (hd : 0 < d) (hu : 0 ≤ u) {δ σ : ℝ} (hδ : 0 < δ) (w : ℕ)
    (hw : (w : ℝ) = σ + δ) {m : ℕ} (hm : m = 0 ∨ d * 2 ^ m ≤ 2) :
    ∑ n ∈ Finset.range m, (u * d ^ w) * ((2 : ℝ) ^ δ) ^ n ≤
      u * ((2 : ℝ) ^ δ / ((2 : ℝ) ^ δ - 1)) * d ^ σ := by
  have hρ : 1 < (2 : ℝ) ^ δ := Real.one_lt_rpow (by norm_num) hδ
  have hρ0 : 0 < (2 : ℝ) ^ δ - 1 := by linarith
  rcases hm with rfl | hm
  · have : 0 ≤ (2 : ℝ) ^ δ / ((2 : ℝ) ^ δ - 1) := div_nonneg (by linarith) hρ0.le
    simp only [Finset.range_zero, Finset.sum_empty]
    exact mul_nonneg (mul_nonneg hu this) (Real.rpow_nonneg hd.le _)
  · rw [← Finset.mul_sum]
    have hd2 : d ^ w = d ^ σ * d ^ δ := by
      rw [← Real.rpow_natCast, hw, Real.rpow_add hd]
    have h1 : ((2 : ℝ) ^ δ) ^ m ≤ (2 / d) ^ δ := by
      rw [two_rpow_pow_eq]
      refine Real.rpow_le_rpow (by positivity) ?_ hδ.le
      rw [le_div_iff₀ hd]; linarith
    have h2 := sum_range_geom_le hρ m
    have h3 : ∑ n ∈ Finset.range m, ((2 : ℝ) ^ δ) ^ n ≤ (2 / d) ^ δ / ((2 : ℝ) ^ δ - 1) :=
      h2.trans (div_le_div_of_nonneg_right h1 hρ0.le)
    calc (u * d ^ w) * ∑ n ∈ Finset.range m, ((2 : ℝ) ^ δ) ^ n
        ≤ (u * d ^ w) * ((2 / d) ^ δ / ((2 : ℝ) ^ δ - 1)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = u * ((2 : ℝ) ^ δ / ((2 : ℝ) ^ δ - 1)) * d ^ σ := by
          rw [hd2, Real.div_rpow (by norm_num) hd.le]
          have : d ^ δ ≠ 0 := (Real.rpow_pos_of_pos hd δ).ne'
          field_simp

end RegularityStructures

end
