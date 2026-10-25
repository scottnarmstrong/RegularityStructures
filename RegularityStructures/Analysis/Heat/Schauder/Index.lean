/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.Conv

/-!
# The splitting index for the Hölder estimate

For `0 < d < 1/4` there is `m : ℕ` with `1/4 < d 2^m ≤ 1/2`.  With `α ∈ (-2, -1)`, `γ = α + 2`,
`ρ = 2^{-(α+1)} > 1` and `r = 2^{-(α+2)} < 1` this gives `d ρ^m ≤ d^γ` and `r^m ≤ 4 d^γ`
(`exists_splitIndex`).  Splitting the shell sum at `m`: the shells `n < m` have
`d 2^n ≤ 1/4` (increment bound), the shells `n ≥ m` are bounded separately.
-/

public section

namespace RegularityStructures

theorem two_rpow_pow_eq (σ : ℝ) (m : ℕ) : ((2 : ℝ) ^ σ) ^ m = ((2 : ℝ) ^ m) ^ σ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
    Real.rpow_natCast]

theorem exists_splitIndex {α d : ℝ} (hα1 : -2 < α) (hα2 : α < -1) (hd : 0 < d) (hd1 : d < 1 / 4) :
    ∃ m : ℕ, (∀ n < m, d * 2 ^ n ≤ 1 / 4) ∧
      d * ((2 : ℝ) ^ (-(α + 1))) ^ m ≤ d ^ (α + 2) ∧
      shellRatio α ^ m ≤ 4 * d ^ (α + 2) := by
  have hex : ∃ m : ℕ, 1 / 4 < d * 2 ^ m := by
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (1 / (4 * d)) (by norm_num : (1 : ℝ) < 2)
    refine ⟨m, ?_⟩
    rw [div_lt_iff₀ (by positivity)] at hm
    linarith
  classical
  set m := Nat.find hex with hm
  have hmspec : 1 / 4 < d * 2 ^ m := Nat.find_spec hex
  have hmin : ∀ n < m, d * 2 ^ n ≤ 1 / 4 := fun n hn => not_lt.1 (Nat.find_min hex hn)
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0] at hmspec
    simp only [pow_zero, mul_one] at hmspec
    linarith
  have hupper : d * 2 ^ m ≤ 1 / 2 := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm0
    have := hmin k (by omega)
    rw [hk, pow_succ]
    linarith
  have ht0 : (0 : ℝ) < 2 ^ m := by positivity
  refine ⟨m, hmin, ?_, ?_⟩
  · have hσ0 : 0 < -(α + 1) := by linarith
    rw [two_rpow_pow_eq]
    have htd : (2 : ℝ) ^ m ≤ d⁻¹ :=
      calc (2 : ℝ) ^ m = ((2 : ℝ) ^ m * d) * d⁻¹ := by field_simp
        _ ≤ 1 * d⁻¹ := mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.2 hd.le)
        _ = d⁻¹ := one_mul _
    have h1 : ((2 : ℝ) ^ m) ^ (-(α + 1)) ≤ (d⁻¹) ^ (-(α + 1)) :=
      Real.rpow_le_rpow ht0.le htd hσ0.le
    have h2 : d ^ (α + 2) = d / d ^ (-(α + 1)) := by
      have : α + 2 = 1 - (-(α + 1)) := by ring
      rw [this, Real.rpow_sub hd, Real.rpow_one]
    rw [h2]
    calc d * ((2 : ℝ) ^ m) ^ (-(α + 1)) ≤ d * (d⁻¹) ^ (-(α + 1)) :=
          mul_le_mul_of_nonneg_left h1 hd.le
      _ = d / d ^ (-(α + 1)) := by rw [Real.inv_rpow hd.le]; ring
  · have hγ0 : 0 < α + 2 := by linarith
    have hγ1 : α + 2 ≤ 1 := by linarith
    have hr : shellRatio α ^ m = (((2 : ℝ) ^ m) ^ (α + 2))⁻¹ := by
      rw [shellRatio, two_rpow_pow_eq, Real.rpow_neg ht0.le]
    rw [hr, ← Real.inv_rpow ht0.le]
    have hlt : ((2 : ℝ) ^ m)⁻¹ ≤ 4 * d := by
      rw [inv_le_comm₀ ht0 (by positivity)]
      rw [inv_eq_one_div, div_le_iff₀ (by positivity)]
      linarith
    calc (((2 : ℝ) ^ m)⁻¹) ^ (α + 2) ≤ (4 * d) ^ (α + 2) :=
          Real.rpow_le_rpow (by positivity) hlt hγ0.le
      _ = 4 ^ (α + 2) * d ^ (α + 2) := Real.mul_rpow (by norm_num) hd.le
      _ ≤ 4 * d ^ (α + 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hd.le _)
          calc (4 : ℝ) ^ (α + 2) ≤ 4 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) hγ1
            _ = 4 := Real.rpow_one 4

end RegularityStructures

end
