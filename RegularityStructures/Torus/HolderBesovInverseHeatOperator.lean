/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HolderBesovInverseHeatKernel
public import RegularityStructures.Torus.HolderBesovHeatFourier
public import RegularityStructures.Torus.HolderBesov
public import RegularityStructures.PDE.HeatOpBridge
import Mathlib.MeasureTheory.Group.LIntegral

/-!
# Recovering LP blocks from their heat regularisation

At time `2^(-2n)`, the dyadic inverse-heat kernel cancels the actual heat multiplier. Its uniform L1
bound gives the LP-to-heat inequality for the heat norm (2.3) of the statement. This module does not
assert the opposite inequality or the full equivalence.
-/

public noncomputable section

open MeasureTheory UnitAddTorus
open scoped ENNReal

namespace RegularityStructures

private theorem character_space_sub (k : Fin 3 → ℤ) (x y : Torus3) :
    mFourier k (x - y) = mFourier k x * mFourier (-k) y := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, Pi.neg_apply,
    fourier_apply, sub_eq_add_neg, zsmul_add, zsmul_neg, neg_zsmul,
    AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

private theorem inverse_convolution (n : ℕ) (g : C(Torus3, ℝ)) (x : Torus3) :
    (∫ y : Torus3, torusDyadicInverseHeatKernel n (x - y) * (g y : ℂ)) =
      ∑ k ∈ torusLPFrequencyBox n,
        ((torusDyadicFrequencySymbol n k : ℂ) * torusInverseHeatWeight n k *
          mFourierCoeff (fun y : Torus3 => (g y : ℂ)) k) * mFourier k x := by
  simp only [torusDyadicInverseHeatKernel, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul, Finset.sum_mul]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    rw [torus_mFourierCoeff_eq_volume_integral]
    calc
      _ = (((torusDyadicFrequencySymbol n k : ℂ) * torusInverseHeatWeight n k) *
          mFourier k x) * ∫ y : Torus3, mFourier (-k) y * (g y : ℂ) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with y
        rw [character_space_sub]
        ring
      _ = _ := mul_right_comm _ _ _
  · intro k _
    exact ((((mFourier k).continuous.comp (continuous_const.sub continuous_id)).const_mul
      ((torusDyadicFrequencySymbol n k : ℂ) * torusInverseHeatWeight n k)).mul
        (Complex.continuous_ofReal.comp g.continuous)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)

private theorem inverse_weight_cancel (n : ℕ) (k : Fin 3 → ℤ) :
    torusInverseHeatWeight n k *
      (∏ i : Fin 3, Complex.exp ((-4 * Real.pi ^ 2 * (((2 : ℝ) ^ n)⁻¹) ^ 2 *
        (k i : ℝ) ^ 2 : ℝ) : ℂ)) = 1 := by
  rw [torusInverseHeatWeight, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro i _
  rw [← Complex.exp_add]
  have he : ((4 * Real.pi ^ 2 * (((2 : ℝ) ^ n)⁻¹ * (k i : ℝ)) ^ 2 : ℝ) : ℂ) +
      ((-4 * Real.pi ^ 2 * (((2 : ℝ) ^ n)⁻¹) ^ 2 * (k i : ℝ) ^ 2 : ℝ) : ℂ) = 0 := by
    push_cast
    ring
  rw [he, Complex.exp_zero]

theorem torusDyadicInverseHeatKernel_recover_block (n : ℕ) (f : C(Torus3, ℝ)) (x : Torus3) :
    torusLittlewoodPaleyBlock n f x =
      ∫ y : Torus3, torusDyadicInverseHeatKernel n (x - y) *
        (PDE.heatOp ((((2 : ℝ) ^ n)⁻¹) ^ 2) f y : ℂ) := by
  have hs : 0 < (((2 : ℝ) ^ n)⁻¹) ^ 2 := sq_pos_of_pos (inv_pos.mpr (pow_pos (by norm_num) _))
  rw [inverse_convolution]
  simp only [torusLittlewoodPaleyBlock, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  have he : mFourierCoeff
      (fun y : Torus3 => (PDE.heatOp ((((2 : ℝ) ^ n)⁻¹) ^ 2) f y : ℂ)) k =
      (∏ i : Fin 3, Complex.exp ((-4 * Real.pi ^ 2 * (((2 : ℝ) ^ n)⁻¹) ^ 2 *
        (k i : ℝ) ^ 2 : ℝ) : ℂ)) * mFourierCoeff (fun y : Torus3 => (f y : ℂ)) k := by
    simp_rw [PDE.heatOp_eq_heatSemigroup hs]
    exact mFourierCoeff_heatSemigroup hs f k
  rw [he]
  have hw := inverse_weight_cancel n k
  calc
    _ = ((torusDyadicFrequencySymbol n k : ℂ) *
        (torusInverseHeatWeight n k * (∏ i : Fin 3,
          Complex.exp ((-4 * Real.pi ^ 2 * (((2 : ℝ) ^ n)⁻¹) ^ 2 *
            (k i : ℝ) ^ 2 : ℝ) : ℂ))) *
        mFourierCoeff (fun y : Torus3 => (f y : ℂ)) k) * mFourier k x := by rw [hw, mul_one]
    _ = _ := by ring

private theorem inverse_convolution_bound (n : ℕ) (g : C(Torus3, ℝ)) (x : Torus3) :
    ‖∫ y : Torus3, torusDyadicInverseHeatKernel n (x - y) * (g y : ℂ)‖ₑ ≤
      (∫⁻ y : Torus3, ‖torusDyadicInverseHeatKernel n y‖ₑ) * ‖g‖ₑ := by
  let : (volume : Measure Torus3).IsNegInvariant :=
    Measure.IsAddHaarMeasure.isNegInvariant_of_regular _
  calc
    _ ≤ ∫⁻ y : Torus3, ‖torusDyadicInverseHeatKernel n (x - y) * (g y : ℂ)‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ y : Torus3, ‖torusDyadicInverseHeatKernel n (x - y)‖ₑ * ‖g‖ₑ := by
      apply lintegral_mono
      intro y
      change ‖torusDyadicInverseHeatKernel n (x - y) * (g y : ℂ)‖ₑ ≤ _
      rw [enorm_mul]
      apply mul_le_mul' le_rfl
      apply enorm_le_iff_norm_le.mpr
      rw [Complex.norm_real]
      exact g.norm_coe_le_norm y
    _ = (∫⁻ y : Torus3, ‖torusDyadicInverseHeatKernel n (x - y)‖ₑ) * ‖g‖ₑ :=
      lintegral_mul_const _ (((torusDyadicInverseHeatKernel n).continuous.comp
        (continuous_const.sub continuous_id)).enorm.measurable)
    _ = _ := congrArg (fun a : ℝ≥0∞ => a * ‖g‖ₑ)
      (lintegral_sub_left_eq_self (fun y : Torus3 => ‖torusDyadicInverseHeatKernel n y‖ₑ) x)

private theorem heat_weight_identity (η : ℝ) (n : ℕ) :
    ((((2 : ℝ) ^ n)⁻¹) ^ 2) ^ (-η / 2) = (2 : ℝ) ^ ((n : ℝ) * η) := by
  have hA : 0 ≤ (2 : ℝ) ^ n := pow_nonneg (by norm_num) _
  have he : ((((2 : ℝ) ^ n)⁻¹) ^ 2) ^ (-η / 2) = ((2 : ℝ) ^ n) ^ η := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (inv_nonneg.mpr hA), Real.inv_rpow hA,
      ← Real.rpow_neg hA]
    congr 1
    ring
  rw [he, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]

theorem torusLittlewoodPaleyENorm_le_holderBesovENorm (η : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : C(Torus3, ℝ),
      torusLittlewoodPaleyENorm η f ≤ ENNReal.ofReal C * holderBesovENorm η f := by
  obtain ⟨C, hC, hb⟩ := lintegral_torusDyadicInverseHeatKernel_bound_uniform
  refine ⟨C + 1, add_pos_of_nonneg_of_pos hC zero_lt_one, ?_⟩
  intro f
  refine iSup_le fun n => ?_
  let s : ℝ := (((2 : ℝ) ^ n)⁻¹) ^ 2
  have hs : 0 < s := sq_pos_of_pos (inv_pos.mpr (pow_pos (by norm_num) _))
  have hs1 : s ≤ 1 := pow_le_one₀ (inv_nonneg.mpr (pow_nonneg (by norm_num) _))
    (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))
  have hop : ‖PDE.heatOp s f‖ₑ = ⨆ x, ‖heatSemigroup s f x‖ₑ := by
    rw [ContinuousMap.enorm_eq_iSup_enorm]
    exact iSup_congr fun x => congrArg (fun a : ℝ => ‖a‖ₑ) (PDE.heatOp_eq_heatSemigroup hs f x)
  have hn : ‖torusLittlewoodPaleyBlock n f‖ₑ ≤ ENNReal.ofReal (C + 1) * ‖PDE.heatOp s f‖ₑ := by
    rw [ContinuousMap.enorm_eq_iSup_enorm]
    refine iSup_le fun x => ?_
    rw [torusDyadicInverseHeatKernel_recover_block]
    exact (inverse_convolution_bound n (PDE.heatOp s f) x).trans
      (mul_le_mul' ((hb n).trans (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right zero_le_one))) le_rfl)
  calc
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ ((n : ℝ) * η)) *
        (ENNReal.ofReal (C + 1) * ‖PDE.heatOp s f‖ₑ) := mul_le_mul' le_rfl hn
    _ = ENNReal.ofReal (C + 1) *
        (ENNReal.ofReal (s ^ (-η / 2)) * ⨆ x, ‖heatSemigroup s f x‖ₑ) := by
      rw [hop]
      dsimp [s]
      rw [heat_weight_identity]
      ring
    _ ≤ _ := mul_le_mul' le_rfl (le_iSup₂ (f := fun r (_ : r ∈ Set.Ioc (0 : ℝ) 1) =>
      ENNReal.ofReal (r ^ (-η / 2)) * ⨆ x, ‖heatSemigroup r f x‖ₑ) s ⟨hs, hs1⟩)

end RegularityStructures

end
