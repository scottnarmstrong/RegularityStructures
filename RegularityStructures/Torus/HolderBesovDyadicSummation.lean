/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# The geometric summation in the heat--Besov comparison

Split a minimum of increasing and decreasing geometric terms where the heat frequency crosses one.
This is the scalar summation step in the equivalence of the heat norm (2.3) of the statement with
the Littlewood--Paley norm.
-/

public noncomputable section

namespace RegularityStructures

theorem torusBesov_tsum_min_geometric_split_le {q r A : ℝ}
    (hq : 1 < q) (hr : 0 ≤ r) (hr1 : r < 1) (hA : 0 ≤ A) (N : ℕ) :
    (∑' n : ℕ, min (q ^ n) (A * r ^ n)) ≤
      q ^ (N + 1) / (q - 1) + A * r ^ (N + 1) / (1 - r) := by
  have hq0 : 0 ≤ q := zero_le_one.trans hq.le
  have hs : Summable (fun n : ℕ => min (q ^ n) (A * r ^ n)) :=
    Summable.of_nonneg_of_le
      (fun n => le_min (pow_nonneg hq0 _) (mul_nonneg hA (pow_nonneg hr _)))
      (fun n => min_le_right _ _) ((summable_geometric_of_lt_one hr hr1).mul_left A)
  have hhead : (∑ n ∈ Finset.range (N + 1), min (q ^ n) (A * r ^ n)) ≤
      q ^ (N + 1) / (q - 1) := by
    calc
      _ ≤ ∑ n ∈ Finset.range (N + 1), q ^ n := Finset.sum_le_sum fun _ _ => min_le_left _ _
      _ = (q ^ (N + 1) - 1) / (q - 1) := geom_sum_eq hq.ne' _
      _ ≤ _ := div_le_div_of_nonneg_right (sub_le_self _ zero_le_one) (sub_nonneg.mpr hq.le)
  have ht := (summable_geometric_of_lt_one hr hr1).mul_left (A * r ^ (N + 1))
  have htail : (∑' n : ℕ, min (q ^ (n + (N + 1))) (A * r ^ (n + (N + 1)))) ≤
      A * r ^ (N + 1) / (1 - r) := by
    calc
      _ ≤ ∑' n : ℕ, (A * r ^ (N + 1)) * r ^ n :=
        Summable.tsum_le_tsum (fun n => (min_le_right _ _).trans_eq (by rw [pow_add]; ring))
          ((summable_nat_add_iff (f := fun n : ℕ => min (q ^ n) (A * r ^ n)) (N + 1)).mpr hs) ht
      _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hr hr1, div_eq_mul_inv]
  rw [← hs.sum_add_tsum_nat_add (N + 1)]
  exact add_le_add hhead htail

theorem torusBesov_tsum_min_rpow_le {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
      (∑' n : ℕ, min ((2 : ℝ) ^ ((n : ℝ) * α))
        (X ^ (α + β) * (2 : ℝ) ^ (-((n : ℝ) * β)))) ≤ C * X ^ α := by
  let q := (2 : ℝ) ^ α
  let r := (2 : ℝ) ^ (-β)
  have hq : 1 < q := Real.one_lt_rpow (by norm_num) hα
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hβ)
  let C := q / (q - 1) + 1 / (1 - r)
  have hC : 0 < C := add_pos (div_pos (zero_lt_one.trans hq) (sub_pos.mpr hq))
    (div_pos zero_lt_one (sub_pos.mpr hr1))
  refine ⟨C, hC, fun X hX => ?_⟩
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  obtain ⟨N, hN, hN'⟩ := exists_nat_pow_near hX (by norm_num : (1 : ℝ) < 2)
  have hqp (n : ℕ) : q ^ n = (2 : ℝ) ^ ((n : ℝ) * α) := by
    dsimp [q]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hrp (n : ℕ) : r ^ n = (2 : ℝ) ^ (-((n : ℝ) * β)) := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hhead : q ^ (N + 1) ≤ q * X ^ α := by
    rw [pow_succ, mul_comm (q ^ N) q]
    apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hq.le)
    have he : q ^ N = ((2 : ℝ) ^ N) ^ α := by
      rw [hqp, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [he]
    exact Real.rpow_le_rpow (pow_nonneg (by norm_num) _) hN hα.le
  have htail : X ^ (α + β) * r ^ (N + 1) ≤ X ^ α := by
    have he : r ^ (N + 1) = ((2 : ℝ) ^ (N + 1)) ^ (-β) := by
      rw [hrp, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    rw [he]
    calc
      _ ≤ X ^ (α + β) * X ^ (-β) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hX0 hN'.le (neg_nonpos.mpr hβ.le)) (Real.rpow_nonneg hX0.le _)
      _ = X ^ α := by rw [← Real.rpow_add hX0]; congr 1; ring
  have hb := torusBesov_tsum_min_geometric_split_le hq hr0 hr1 (Real.rpow_nonneg hX0.le (α + β)) N
  simp_rw [hqp, hrp] at hb
  calc
    _ ≤ q ^ (N + 1) / (q - 1) + X ^ (α + β) * r ^ (N + 1) / (1 - r) := by
      simpa only [hqp, hrp] using hb
    _ ≤ (q * X ^ α) / (q - 1) + X ^ α / (1 - r) := add_le_add
      (div_le_div_of_nonneg_right hhead (sub_nonneg.mpr hq.le))
      (div_le_div_of_nonneg_right htail (sub_nonneg.mpr hr1.le))
    _ = C * X ^ α := by dsimp [C]; ring

theorem torusBesov_tsum_heat_scale_le (η : ℝ) (hη : η < 0) (M : ℕ)
    (hM : 0 < 2 * (M : ℝ) + η) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 0 < s → s ≤ 1 →
      (∑' n : ℕ, min ((2 : ℝ) ^ (-((n : ℝ) * η)))
        (s ^ (-(M : ℝ)) * (2 : ℝ) ^ (-((n : ℝ) * (2 * (M : ℝ) + η))))) ≤
          C * s ^ (η / 2) := by
  obtain ⟨C, hC, hb⟩ := torusBesov_tsum_min_rpow_le (neg_pos.mpr hη) hM
  refine ⟨C, hC, fun s hs hs1 => ?_⟩
  have hroot : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hroot1 : Real.sqrt s ≤ 1 := (Real.sqrt_le_one).mpr hs1
  have hX : 1 ≤ (Real.sqrt s)⁻¹ := by
    simpa only [one_div, inv_one] using (one_div_le_one_div_of_le hroot hroot1)
  have hA : ((Real.sqrt s)⁻¹) ^ (-η + (2 * (M : ℝ) + η)) = s ^ (-(M : ℝ)) := by
    have he : -η + (2 * (M : ℝ) + η) = ((2 * M : ℕ) : ℝ) := by push_cast; ring
    rw [he, Real.rpow_natCast, Real.rpow_neg hs.le, Real.rpow_natCast,
      inv_pow, pow_mul, Real.sq_sqrt hs.le]
  have hXpow : ((Real.sqrt s)⁻¹) ^ (-η) = s ^ (η / 2) := by
    rw [Real.inv_rpow (Real.sqrt_nonneg s), ← Real.rpow_neg (Real.sqrt_nonneg s),
      neg_neg, Real.sqrt_eq_rpow, ← Real.rpow_mul hs.le]
    congr 1
    ring
  simpa only [hA, hXpow, mul_neg] using hb (Real.sqrt s)⁻¹ hX

end RegularityStructures

end
