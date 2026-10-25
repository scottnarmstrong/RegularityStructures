/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HolderBesovAnnularHeatBound
public import RegularityStructures.Torus.HolderBesovDyadicSummation

/-!
# Summing the heat-regularised LP blocks

The exact dyadic weights turn the contraction/decay minimum into the geometric series at the heat
scale. This is the summation input to the reverse inequality in the equivalence of the heat norm
(2.3) of the statement with the Littlewood--Paley norm.
-/

public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace RegularityStructures

theorem enorm_torusLittlewoodPaleyBlock_le_ENorm (η : ℝ) (f : C(Torus3, ℝ)) (n : ℕ) :
    ‖torusLittlewoodPaleyBlock n f‖ₑ ≤
      ENNReal.ofReal ((2 : ℝ) ^ (-((n : ℝ) * η))) * torusLittlewoodPaleyENorm η f := by
  have he : ENNReal.ofReal ((2 : ℝ) ^ (-((n : ℝ) * η))) *
      ENNReal.ofReal ((2 : ℝ) ^ ((n : ℝ) * η)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), neg_add_cancel,
      Real.rpow_zero, ENNReal.ofReal_one]
  calc
    _ = ENNReal.ofReal ((2 : ℝ) ^ (-((n : ℝ) * η))) *
        (ENNReal.ofReal ((2 : ℝ) ^ ((n : ℝ) * η)) * ‖torusLittlewoodPaleyBlock n f‖ₑ) := by
      rw [← mul_assoc, he, one_mul]
    _ ≤ _ := mul_le_mul' le_rfl (le_iSup
      (fun j : ℕ => ENNReal.ofReal ((2 : ℝ) ^ ((j : ℝ) * η)) * ‖torusLittlewoodPaleyBlock j f‖ₑ) n)

private theorem inverse_dyadic_pow (n M : ℕ) :
    (((2 : ℝ) ^ n)⁻¹) ^ (2 * M) = (2 : ℝ) ^ (-((n : ℝ) * (2 * (M : ℝ)))) := by
  calc
    _ = ((2 : ℝ) ^ n) ^ (-((2 * M : ℕ) : ℝ)) := by
      rw [Real.rpow_neg (pow_nonneg (by norm_num) _), Real.rpow_natCast, inv_pow]
    _ = _ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      push_cast
      ring

private theorem successor_weight_min_identity (η s C : ℝ) (n M : ℕ) :
    C * min (1 : ℝ) (s ^ (-(M : ℝ)) * (((2 : ℝ) ^ n)⁻¹) ^ (2 * M)) *
      (2 : ℝ) ^ (-(((n + 1 : ℕ) : ℝ) * η)) =
      (C * (2 : ℝ) ^ (-η)) * min ((2 : ℝ) ^ (-((n : ℝ) * η)))
        (s ^ (-(M : ℝ)) * (2 : ℝ) ^ (-((n : ℝ) * (2 * (M : ℝ) + η)))) := by
  have he : (2 : ℝ) ^ (-(((n + 1 : ℕ) : ℝ) * η)) =
      (2 : ℝ) ^ (-η) * (2 : ℝ) ^ (-((n : ℝ) * η)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    push_cast
    ring
  have hp : (((2 : ℝ) ^ n)⁻¹) ^ (2 * M) * (2 : ℝ) ^ (-((n : ℝ) * η)) =
      (2 : ℝ) ^ (-((n : ℝ) * (2 * (M : ℝ) + η))) := by
    rw [inverse_dyadic_pow, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [he]
  calc
    _ = (C * (2 : ℝ) ^ (-η)) *
        (min (1 : ℝ) (s ^ (-(M : ℝ)) * (((2 : ℝ) ^ n)⁻¹) ^ (2 * M)) *
          (2 : ℝ) ^ (-((n : ℝ) * η))) := by ring
    _ = _ := by
      have hinner : s ^ (-(M : ℝ)) * (((2 : ℝ) ^ n)⁻¹) ^ (2 * M) *
          (2 : ℝ) ^ (-((n : ℝ) * η)) =
          s ^ (-(M : ℝ)) * (2 : ℝ) ^ (-((n : ℝ) * (2 * (M : ℝ) + η))) := by
        rw [mul_assoc, hp]
      rw [min_mul_of_nonneg _ _ (Real.rpow_nonneg (by norm_num) _), one_mul, hinner]

theorem tsum_enorm_heatOp_torusLittlewoodPaleyBlock_tail_le (η : ℝ) (hη : η < 0) (M : ℕ)
    (hM : 0 < 2 * (M : ℝ) + η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ f : C(Torus3, ℝ),
      (∑' n : ℕ, ‖PDE.heatOp s (torusLittlewoodPaleyBlock (n + 1) f)‖ₑ) ≤
        ENNReal.ofReal (C * s ^ (η / 2)) * torusLittlewoodPaleyENorm η f := by
  obtain ⟨A, hA, hb⟩ := enorm_heatOp_torusLittlewoodPaleyBlock_succ_min_bound M
  obtain ⟨K, hK, hsum⟩ := torusBesov_tsum_heat_scale_le η hη M hM
  let D := A * (2 : ℝ) ^ (-η)
  have hD : 0 ≤ D := mul_nonneg hA (Real.rpow_nonneg (by norm_num) _)
  refine ⟨D * K, mul_nonneg hD hK.le, fun s hs hs1 f => ?_⟩
  let F : ℕ → ℝ := fun n => min ((2 : ℝ) ^ (-((n : ℝ) * η)))
    (s ^ (-(M : ℝ)) * (2 : ℝ) ^ (-((n : ℝ) * (2 * (M : ℝ) + η))))
  have hF0 (n : ℕ) : 0 ≤ F n := le_min (Real.rpow_nonneg (by norm_num) _)
    (mul_nonneg (Real.rpow_nonneg hs.le _) (Real.rpow_nonneg (by norm_num) _))
  have hgeom : Summable (fun n : ℕ => (2 : ℝ) ^ (-((n : ℝ) * (2 * (M : ℝ) + η)))) := by
    convert summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-(2 * (M : ℝ) + η)))
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) (neg_neg_of_pos hM)) using 1
    funext n
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hFs : Summable F := Summable.of_nonneg_of_le hF0 (fun n => min_le_right _ _)
    (hgeom.mul_left (s ^ (-(M : ℝ))))
  have hpoint (n : ℕ) : ‖PDE.heatOp s (torusLittlewoodPaleyBlock (n + 1) f)‖ₑ ≤
      ENNReal.ofReal (D * F n) * torusLittlewoodPaleyENorm η f := by
    have hmin : 0 ≤ A * min (1 : ℝ) (s ^ (-(M : ℝ)) * (((2 : ℝ) ^ n)⁻¹) ^ (2 * M)) :=
      mul_nonneg hA (le_min zero_le_one (mul_nonneg (Real.rpow_nonneg hs.le _)
        (pow_nonneg (inv_nonneg.mpr (pow_nonneg (by norm_num) _)) _)))
    calc
      _ ≤ ENNReal.ofReal (A * min (1 : ℝ) (s ^ (-(M : ℝ)) * (((2 : ℝ) ^ n)⁻¹) ^ (2 * M))) *
          (ENNReal.ofReal ((2 : ℝ) ^ (-(((n + 1 : ℕ) : ℝ) * η))) * torusLittlewoodPaleyENorm η f) :=
        (hb s hs n f).trans (mul_le_mul' le_rfl (enorm_torusLittlewoodPaleyBlock_le_ENorm η f (n + 1)))
      _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hmin, successor_weight_min_identity]
  calc
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (D * F n) * torusLittlewoodPaleyENorm η f :=
      ENNReal.tsum_le_tsum hpoint
    _ = ENNReal.ofReal (D * ∑' n : ℕ, F n) * torusLittlewoodPaleyENorm η f := by
      rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg
        (fun n => mul_nonneg hD (hF0 n)) (hFs.mul_left D), tsum_mul_left]
    _ ≤ ENNReal.ofReal (D * (K * s ^ (η / 2))) * torusLittlewoodPaleyENorm η f :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hsum s hs hs1) hD)) le_rfl
    _ = _ := congrArg (fun a : ℝ => ENNReal.ofReal a * torusLittlewoodPaleyENorm η f)
      (mul_assoc D K (s ^ (η / 2))).symm

end RegularityStructures

end
