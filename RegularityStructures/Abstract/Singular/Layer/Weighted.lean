/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Layer.Pair
public import RegularityStructures.Abstract.Singular.Layer.Sums

/-!
# Summing the weight bound over the time indices of a box

For `0 ≤ θ < 2`, `λ ≤ 1`, `Λ = λ 2^n ≥ 1` and a finite set `I` of time indices with
`|I| ≤ 11 Λ²`,
`∑_{j ∈ I, j > 0} 2^θ (1 + (2^{-(n+1)} √j)^{-θ}) ≤ κ Λ² λ^{-θ}`, `κ = 11 · 2^θ (1 + 2^θ/(1 - θ/2))`.
-/

public section

namespace RegularityStructures.Layer

theorem weightBound_eq {θ : ℝ} {m : ℕ} {j : ℤ} (hj : 1 ≤ j) :
    weightBound θ m j = (2 : ℝ) ^ θ * (1 + ((2 : ℝ) ^ m) ^ θ * ((j : ℤ) : ℝ) ^ (-(θ / 2))) := by
  have hj0 : (0 : ℝ) ≤ (j : ℤ) := by exact_mod_cast (by omega : (0 : ℤ) ≤ j)
  unfold weightBound
  congr 2
  rw [Real.mul_rpow (by positivity) (Real.sqrt_nonneg _), Real.inv_rpow (by positivity),
    Real.rpow_neg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ m), inv_inv, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hj0]
  congr 2
  ring

private theorem rpow_identity {θ : ℝ} {n : ℕ} {lam : ℝ} (hlam : 0 < lam) :
    ((2 : ℝ) ^ n) ^ θ * (lam * 2 ^ n) ^ (-θ) = lam ^ (-θ) := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  rw [Real.mul_rpow hlam.le h2.le, mul_left_comm, Real.rpow_neg h2.le, mul_inv_cancel₀
    (Real.rpow_pos_of_pos h2 _).ne', mul_one]

theorem sum_weightBound_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ2 : θ < 2) {n : ℕ} {lam : ℝ}
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (I : Finset ℤ)
    (hI : (I.card : ℝ) ≤ 11 * (lam * 2 ^ n) ^ 2) :
    ∑ j ∈ I, (if 0 < j then weightBound θ (n + 1) j else 0) ≤
      11 * (2 : ℝ) ^ θ * (1 + (2 : ℝ) ^ θ / (1 - θ / 2)) * (lam * 2 ^ n) ^ 2 * lam ^ (-θ) := by
  set Λ : ℝ := lam * 2 ^ n with hΛ_def
  have hΛ0 : 0 < Λ := by positivity
  have hb : 0 < 1 - θ / 2 := by linarith
  have hP : ∑ j ∈ I, (if 0 < j then weightBound θ (n + 1) j else 0) =
      ∑ j ∈ I.filter (fun j => 0 < j), weightBound θ (n + 1) j := (Finset.sum_filter _ _).symm
  rw [hP]
  set P := I.filter (fun j => 0 < j) with hP_def
  have hPI : (P.card : ℝ) ≤ 11 * Λ ^ 2 :=
    le_trans (by exact_mod_cast Finset.card_filter_le _ _) hI
  have hS : ∑ j ∈ P, weightBound θ (n + 1) j =
      (2 : ℝ) ^ θ * ((P.card : ℝ) + ((2 : ℝ) ^ (n + 1)) ^ θ *
        ∑ j ∈ P, ((j : ℤ) : ℝ) ^ (-(θ / 2))) := by
    have hS1 : ∀ j ∈ P, weightBound θ (n + 1) j =
        (2 : ℝ) ^ θ * (1 + ((2 : ℝ) ^ (n + 1)) ^ θ * ((j : ℤ) : ℝ) ^ (-(θ / 2))) :=
      fun j hj => weightBound_eq (by have := (Finset.mem_filter.1 hj).2; omega)
    rw [Finset.sum_congr rfl hS1]
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
  have hR := sum_rpow_neg_le (b := θ / 2) (by linarith) (by linarith) P
    fun j hj => (Finset.mem_filter.1 hj).2
  have hRp : (P.card : ℝ) ^ (1 - θ / 2) ≤ (11 * Λ ^ 2) ^ (1 - θ / 2) :=
    Real.rpow_le_rpow (by positivity) hPI hb.le
  have h11 : (11 * Λ ^ 2) ^ (1 - θ / 2) ≤ 11 * Λ ^ (2 - θ) := by
    rw [Real.mul_rpow (by norm_num) (by positivity)]
    have e1 : (Λ ^ 2) ^ (1 - θ / 2) = Λ ^ (2 - θ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hΛ0.le]
      congr 1; push_cast; ring
    rw [e1]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hΛ0.le _)
    calc (11 : ℝ) ^ (1 - θ / 2) ≤ 11 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 11 := Real.rpow_one _
  have e2 : Λ ^ (2 - θ) = Λ ^ 2 * Λ ^ (-θ) := by
    rw [sub_eq_add_neg, Real.rpow_add hΛ0, ← Real.rpow_natCast]
    norm_num
  have e3 : ((2 : ℝ) ^ (n + 1)) ^ θ = (2 : ℝ) ^ θ * ((2 : ℝ) ^ n) ^ θ := by
    rw [pow_succ, Real.mul_rpow (by positivity) (by norm_num), mul_comm]
  have hE : ((2 : ℝ) ^ (n + 1)) ^ θ * (P.card : ℝ) ^ (1 - θ / 2) ≤
      (2 : ℝ) ^ θ * (11 * Λ ^ 2 * lam ^ (-θ)) := by
    calc ((2 : ℝ) ^ (n + 1)) ^ θ * (P.card : ℝ) ^ (1 - θ / 2)
        ≤ ((2 : ℝ) ^ (n + 1)) ^ θ * (11 * Λ ^ (2 - θ)) :=
          mul_le_mul_of_nonneg_left (hRp.trans h11) (Real.rpow_nonneg (by positivity) _)
      _ = (2 : ℝ) ^ θ * (11 * Λ ^ 2 * (((2 : ℝ) ^ n) ^ θ * Λ ^ (-θ))) := by
          rw [e3, e2]; ring
      _ = _ := by rw [hΛ_def, rpow_identity hlam]
  have hl1 : 1 ≤ lam ^ (-θ) := by
    rw [Real.rpow_neg hlam.le]
    exact one_le_inv₀ (Real.rpow_pos_of_pos hlam _) |>.2 (Real.rpow_le_one hlam.le hlam1 hθ0)
  have hEb : ((2 : ℝ) ^ (n + 1)) ^ θ * ∑ j ∈ P, ((j : ℤ) : ℝ) ^ (-(θ / 2)) ≤
      (2 : ℝ) ^ θ * (11 * Λ ^ 2 * lam ^ (-θ)) / (1 - θ / 2) := by
    calc _ ≤ ((2 : ℝ) ^ (n + 1)) ^ θ * ((P.card : ℝ) ^ (1 - θ / 2) / (1 - θ / 2)) :=
          mul_le_mul_of_nonneg_left hR (Real.rpow_nonneg (by positivity) _)
      _ = ((2 : ℝ) ^ (n + 1)) ^ θ * (P.card : ℝ) ^ (1 - θ / 2) / (1 - θ / 2) := by ring
      _ ≤ _ := by gcongr
  rw [hS]
  have h2θ : (1 : ℝ) ≤ (2 : ℝ) ^ θ := Real.one_le_rpow (by norm_num) hθ0
  have hΛ2 : 0 ≤ Λ ^ 2 := by positivity
  calc (2 : ℝ) ^ θ * ((P.card : ℝ) + ((2 : ℝ) ^ (n + 1)) ^ θ *
        ∑ j ∈ P, ((j : ℤ) : ℝ) ^ (-(θ / 2)))
      ≤ (2 : ℝ) ^ θ * (11 * Λ ^ 2 + (2 : ℝ) ^ θ * (11 * Λ ^ 2 * lam ^ (-θ)) / (1 - θ / 2)) := by
        gcongr
    _ ≤ (2 : ℝ) ^ θ * (11 * Λ ^ 2 * lam ^ (-θ) *
          (1 + (2 : ℝ) ^ θ / (1 - θ / 2))) := by
        gcongr
        have : 11 * Λ ^ 2 ≤ 11 * Λ ^ 2 * lam ^ (-θ) := le_mul_of_one_le_right (by positivity) hl1
        rw [mul_add, mul_one]
        refine add_le_add this (le_of_eq ?_)
        ring
    _ = _ := by ring

end RegularityStructures.Layer

end
