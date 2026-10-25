/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HolderBesovAnnularHeatIdentity

/-!
# Annular heat decay without a frequency-counting loss

Compose the fixed Green multiplier kernels with the coordinate-weighted heat kernels and use their
actual L1 bounds. Their exact symbol identity gives the inverse frequency power. This proves the
annular decay input to the equivalence of the heat norm (2.3) of the statement with the
Littlewood--Paley norm.
-/

public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace RegularityStructures

theorem enorm_heatOp_torusLittlewoodPaleyBlock_succ_bound (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 < s → ∀ n : ℕ, ∀ f : C(Torus3, ℝ),
      ‖PDE.heatOp s (torusLittlewoodPaleyBlock (n + 1) f)‖ₑ ≤
        ENNReal.ofReal (C * s ^ (-(M : ℝ)) * (((2 : ℝ) ^ (n + 2))⁻¹) ^ (2 * M)) *
          ‖torusLittlewoodPaleyBlock (n + 1) f‖ₑ := by
  have hGreen := fun i : Fin 3 => lintegral_torusLPAnnulusGreenKernel_bound_uniform M i
  choose G hG hGb using hGreen
  have hHeat := fun i : Fin 3 => lintegral_torusWeightedHeatKernel_time_bound M i
  choose H hH hHb using hHeat
  let C : ℝ := ∑ i : Fin 3, H i * G i
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ => mul_nonneg (hH i) (hG i)
  refine ⟨C, hC, fun s hs n f => ?_⟩
  let B := torusLittlewoodPaleyBlock (n + 1) f
  have ht (i : Fin 3) : ‖torusAnnularHeatTerm M i n s hs f‖ₑ ≤
      ENNReal.ofReal (H i * s ^ (-(M : ℝ)) * G i) * ‖B‖ₑ := by
    have hh : (∫⁻ x : Torus3, ‖torusWeightedHeatKernelMap M i s hs x‖ₑ) ≤
        ENNReal.ofReal (H i * s ^ (-(M : ℝ))) := hHb i s hs
    have hg := hGb i n
    calc
      _ ≤ (∫⁻ x : Torus3, ‖torusWeightedHeatKernelMap M i s hs x‖ₑ) *
          ‖torusMultiplierAction (torusLPAnnulusGreenKernel M i n) B‖ₑ :=
        enorm_torusMultiplierAction_le _ _
      _ ≤ ENNReal.ofReal (H i * s ^ (-(M : ℝ))) *
          (ENNReal.ofReal (G i) * ‖B‖ₑ) := mul_le_mul' hh
        ((enorm_torusMultiplierAction_le _ _).trans (mul_le_mul' hg le_rfl))
      _ = _ := by
        rw [ENNReal.ofReal_mul (mul_nonneg (hH i) (Real.rpow_nonneg hs.le _))]
        ring
  have hsum : (∑ i : Fin 3, ENNReal.ofReal (H i * s ^ (-(M : ℝ)) * G i)) =
      ENNReal.ofReal (C * s ^ (-(M : ℝ))) := by
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun i _ => mul_nonneg (mul_nonneg (hH i) (Real.rpow_nonneg hs.le _)) (hG i))]
    congr 1
    dsimp [C]
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hscalar : ‖((((2 : ℝ) ^ (n + 2))⁻¹ : ℝ) : ℂ) ^ (2 * M)‖ₑ =
      ENNReal.ofReal ((((2 : ℝ) ^ (n + 2))⁻¹) ^ (2 * M)) := by
    rw [← ofReal_norm, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (pow_pos (by norm_num) _))]
  rw [heatOp_torusLittlewoodPaleyBlock_succ_eq_annular M n s hs f, enorm_smul, hscalar]
  calc
    _ ≤ ENNReal.ofReal ((((2 : ℝ) ^ (n + 2))⁻¹) ^ (2 * M)) *
        ∑ i : Fin 3, ‖torusAnnularHeatTerm M i n s hs f‖ₑ :=
      mul_le_mul' le_rfl (enorm_sum_le Finset.univ
        (fun i : Fin 3 => torusAnnularHeatTerm M i n s hs f))
    _ ≤ ENNReal.ofReal ((((2 : ℝ) ^ (n + 2))⁻¹) ^ (2 * M)) *
        ∑ i : Fin 3, ENNReal.ofReal (H i * s ^ (-(M : ℝ)) * G i) * ‖B‖ₑ :=
      mul_le_mul' le_rfl (Finset.sum_le_sum fun i _ => ht i)
    _ = ENNReal.ofReal ((((2 : ℝ) ^ (n + 2))⁻¹) ^ (2 * M)) *
        (ENNReal.ofReal (C * s ^ (-(M : ℝ))) * ‖B‖ₑ) := by rw [← Finset.sum_mul, hsum]
    _ = _ := by
      rw [ENNReal.ofReal_mul (mul_nonneg hC (Real.rpow_nonneg hs.le _))]
      ring

theorem enorm_heatOp_torusLittlewoodPaleyBlock_succ_min_bound (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 < s → ∀ n : ℕ, ∀ f : C(Torus3, ℝ),
      ‖PDE.heatOp s (torusLittlewoodPaleyBlock (n + 1) f)‖ₑ ≤
        ENNReal.ofReal (C * min (1 : ℝ)
          (s ^ (-(M : ℝ)) * (((2 : ℝ) ^ n)⁻¹) ^ (2 * M))) *
            ‖torusLittlewoodPaleyBlock (n + 1) f‖ₑ := by
  obtain ⟨C₀, hC₀, hb⟩ := enorm_heatOp_torusLittlewoodPaleyBlock_succ_bound M
  let C := max C₀ 1
  have hC : 0 ≤ C := hC₀.trans (le_max_left _ _)
  have hC1 : 1 ≤ C := le_max_right _ _
  refine ⟨C, hC, fun s hs n f => ?_⟩
  let B := s ^ (-(M : ℝ)) * (((2 : ℝ) ^ n)⁻¹) ^ (2 * M)
  have hinv : (((2 : ℝ) ^ (n + 2))⁻¹) ^ (2 * M) ≤
      (((2 : ℝ) ^ n)⁻¹) ^ (2 * M) := by
    apply pow_le_pow_left₀ (inv_nonneg.mpr (pow_nonneg (by norm_num) _))
    have he := one_div_le_one_div_of_le (pow_pos (by norm_num : (0 : ℝ) < 2) n)
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_add_right n 2))
    simpa only [one_div] using he
  have hcoef : C₀ * s ^ (-(M : ℝ)) * (((2 : ℝ) ^ (n + 2))⁻¹) ^ (2 * M) ≤ C * B := by
    calc
      _ ≤ C * s ^ (-(M : ℝ)) * (((2 : ℝ) ^ n)⁻¹) ^ (2 * M) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hs.le _))
          hinv (pow_nonneg (inv_nonneg.mpr (pow_nonneg (by norm_num) _)) _)
            (mul_nonneg hC (Real.rpow_nonneg hs.le _))
      _ = C * B := by dsimp [B]; ring
  have hdecay := (hb s hs n f).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hcoef) le_rfl)
  have hcontract : ‖PDE.heatOp s (torusLittlewoodPaleyBlock (n + 1) f)‖ₑ ≤
      ‖torusLittlewoodPaleyBlock (n + 1) f‖ₑ :=
    enorm_le_iff_norm_le.mpr (PDE.norm_heatOp_le s _)
  by_cases hB : B ≤ 1
  · rw [min_eq_right hB]
    exact hdecay
  · rw [min_eq_left (le_of_not_ge hB), mul_one]
    apply hcontract.trans
    have he : (1 : ℝ≥0∞) ≤ ENNReal.ofReal C := by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hC1
    simpa only [one_mul] using mul_le_mul' he
      (le_refl ‖torusLittlewoodPaleyBlock (n + 1) f‖ₑ)

end RegularityStructures

end

