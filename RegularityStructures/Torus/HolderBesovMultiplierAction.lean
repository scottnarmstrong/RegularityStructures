/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HolderBesovHeatFourier
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Group.LIntegral

/-!
# Convolution actions of continuous torus multiplier kernels

Continuous kernels act on continuous functions by convolution. Character eigenvalues are exactly
their Fourier coefficients, and the operator norm is bounded by the L1 kernel norm. This is the
composition step towards annular heat decay in the equivalence of the heat norm (2.3) of the
statement with the Littlewood--Paley norm.
-/

@[expose] public noncomputable section

open MeasureTheory UnitAddTorus
open scoped ENNReal Convolution

namespace RegularityStructures

/-- Convolution by a continuous periodic Fourier-multiplier kernel. -/
def torusMultiplierAction (K g : C(Torus3, ℂ)) : C(Torus3, ℂ) where
  toFun x := ∫ y : Torus3, K (x - y) * g y
  continuous_toFun := by
    have hc := (HasCompactSupport.of_compactSpace (K : Torus3 → ℂ)).continuous_convolution_right
      (L := ContinuousLinearMap.mul ℝ ℂ) (μ := (volume : Measure Torus3))
        g.continuous.locallyIntegrable K.continuous
    convert hc using 1
    funext x
    apply integral_congr_ae
    filter_upwards [] with y
    exact mul_comm _ _

theorem torusMultiplierAction_apply (K g : C(Torus3, ℂ)) (x : Torus3) :
    torusMultiplierAction K g x = ∫ y : Torus3, K (x - y) * g y := rfl

private theorem character_space_sub (k : Fin 3 → ℤ) (x y : Torus3) :
    mFourier k (x - y) = mFourier k x * mFourier (-k) y := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, Pi.neg_apply,
    fourier_apply, sub_eq_add_neg, zsmul_add, zsmul_neg, neg_zsmul,
    AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

theorem torusMultiplierAction_mFourier (K : C(Torus3, ℂ)) (k : Fin 3 → ℤ) :
    torusMultiplierAction K (mFourier k) = mFourierCoeff K k • mFourier k := by
  let : (volume : Measure Torus3).IsNegInvariant :=
    Measure.IsAddHaarMeasure.isNegInvariant_of_regular _
  ext x
  rw [torusMultiplierAction_apply]
  calc
    _ = ∫ y : Torus3, K y * mFourier k (x - y) := by
      have h := integral_sub_left_eq_self (fun y : Torus3 => K (x - y) * mFourier k y) volume x
      simpa only [sub_sub_cancel] using h.symm
    _ = (∫ y : Torus3, mFourier (-k) y * K y) * mFourier k x := by
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [] with y
      rw [character_space_sub]
      ring
    _ = _ := by rw [torus_mFourierCoeff_eq_volume_integral]; rfl

theorem torusMultiplierAction_smul (K g : C(Torus3, ℂ)) (c : ℂ) :
    torusMultiplierAction K (c • g) = c • torusMultiplierAction K g := by
  ext x
  simp only [torusMultiplierAction_apply, ContinuousMap.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  ring

theorem torusMultiplierAction_sum {ι : Type*} (K : C(Torus3, ℂ))
    (S : Finset ι) (g : ι → C(Torus3, ℂ)) :
    torusMultiplierAction K (∑ j ∈ S, g j) = ∑ j ∈ S, torusMultiplierAction K (g j) := by
  ext x
  simp only [torusMultiplierAction_apply, ContinuousMap.sum_apply, Finset.mul_sum]
  rw [integral_finsetSum]
  intro j _
  exact ((K.continuous.comp (continuous_const.sub continuous_id)).mul
    (g j).continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem torusMultiplierAction_fourierSum (K : C(Torus3, ℂ))
    (S : Finset (Fin 3 → ℤ)) (c : (Fin 3 → ℤ) → ℂ) :
    torusMultiplierAction K (∑ k ∈ S, c k • mFourier k) =
      ∑ k ∈ S, (c k * mFourierCoeff K k) • mFourier k := by
  rw [torusMultiplierAction_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [torusMultiplierAction_smul, torusMultiplierAction_mFourier, smul_smul]

theorem enorm_torusMultiplierAction_le (K g : C(Torus3, ℂ)) :
    ‖torusMultiplierAction K g‖ₑ ≤ (∫⁻ y : Torus3, ‖K y‖ₑ) * ‖g‖ₑ := by
  let : (volume : Measure Torus3).IsNegInvariant :=
    Measure.IsAddHaarMeasure.isNegInvariant_of_regular _
  rw [ContinuousMap.enorm_eq_iSup_enorm]
  refine iSup_le fun x => ?_
  rw [torusMultiplierAction_apply]
  calc
    _ ≤ ∫⁻ y : Torus3, ‖K (x - y) * g y‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ y : Torus3, ‖K (x - y)‖ₑ * ‖g‖ₑ := by
      apply lintegral_mono
      intro y
      change ‖K (x - y) * g y‖ₑ ≤ ‖K (x - y)‖ₑ * ‖g‖ₑ
      rw [enorm_mul]
      exact mul_le_mul' le_rfl (enorm_le_iff_norm_le.mpr (g.norm_coe_le_norm y))
    _ = (∫⁻ y : Torus3, ‖K (x - y)‖ₑ) * ‖g‖ₑ :=
      lintegral_mul_const _ ((K.continuous.comp (continuous_const.sub continuous_id)).enorm.measurable)
    _ = _ := congrArg (fun a : ℝ≥0∞ => a * ‖g‖ₑ)
      (lintegral_sub_left_eq_self (fun y : Torus3 => ‖K y‖ₑ) x)

end RegularityStructures

end
