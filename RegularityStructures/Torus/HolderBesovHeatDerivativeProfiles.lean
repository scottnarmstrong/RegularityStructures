/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HolderBesovTensorMultiplier
public import RegularityStructures.Torus.HolderBesovSchwartzCoefficients
public import RegularityStructures.Analysis.Kernel.Schwartz
public import Mathlib.Analysis.Distribution.TemperateGrowth

/-!
# Weighted heat Fourier kernels from fixed Schwartz profiles

The coordinate polynomial times a Gaussian is a fixed Schwartz profile. At frequency scale `a`, its
tensor periodisation has L1 norm bounded by `C_M a^(2M)`. Setting `a=s^(-1/2)` gives the derivative
heat bound needed for annular decay in the equivalence of the heat norm (2.3) of the statement with
the Littlewood--Paley norm. No classical derivative estimate is used as a hypothesis.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal SchwartzMap

namespace RegularityStructures

/-- The fixed profile `u^(2M) exp(-4 pi^2 u^2)`. -/
def torusHeatDerivativeProfile (M : ℕ) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun u : ℝ => (u : ℂ) ^ (2 * M))
    (expPowSchwartz (mul_pos (by norm_num : (0 : ℝ) < 4)
      (sq_pos_of_pos Real.pi_pos)) (by norm_num : 0 < (1 : ℕ)))

theorem torusHeatDerivativeProfile_apply (M : ℕ) (u : ℝ) :
    torusHeatDerivativeProfile M u = (u : ℂ) ^ (2 * M) *
      ((Real.exp (-(4 * Real.pi ^ 2 * u ^ 2)) : ℝ) : ℂ) := by
  have hp : Function.HasTemperateGrowth (fun u : ℝ => (u : ℂ) ^ (2 * M)) := by
    convert Complex.ofRealCLM.hasTemperateGrowth.pow (2 * M) using 1
    funext u
    rfl
  rw [torusHeatDerivativeProfile, SchwartzMap.smulLeftCLM_apply_apply hp, expPowSchwartz_apply]
  simp only [mul_one, smul_eq_mul]

/-- The tensor Fourier kernel with `2M` powers in coordinate `i` at frequency scale `a`. -/
def torusWeightedHeatKernel (M : ℕ) (i : Fin 3) (a : ℝ) (x : Torus3) : ℂ :=
  (a : ℂ) ^ (2 * M) * ∏ j : Fin 3, ∑' k : ℤ,
    torusHeatDerivativeProfile (if j = i then M else 0) ((k : ℝ) / a) * fourier k (x j)

theorem continuous_torusWeightedHeatKernel (M : ℕ) (i : Fin 3) {a : ℝ} (ha : 0 < a) :
    Continuous (torusWeightedHeatKernel M i a) := by
  apply continuous_const.mul
  apply continuous_finsetProd
  intro j _
  exact (continuous_schwartz_multiplier_circle
    (torusHeatDerivativeProfile (if j = i then M else 0)) ha).comp (continuous_apply j)

theorem lintegral_torusWeightedHeatKernel_bound_uniform (M : ℕ) (i : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 < a →
      (∫⁻ x : Torus3, ‖torusWeightedHeatKernel M i a x‖ₑ) ≤
        ENNReal.ofReal (C * a ^ (2 * M)) := by
  obtain ⟨C, hC, hb⟩ := schwartz_torus_tensor_multiplier_bound_uniform
    (fun j : Fin 3 => torusHeatDerivativeProfile (if j = i then M else 0))
  refine ⟨C, hC, fun a ha => ?_⟩
  have hm : Measurable (fun x : Torus3 =>
      ‖∏ j : Fin 3, ∑' k : ℤ,
        torusHeatDerivativeProfile (if j = i then M else 0) ((k : ℝ) / a) * fourier k (x j)‖ₑ) := by
    apply Continuous.measurable
    apply Continuous.enorm
    apply continuous_finsetProd
    intro j _
    exact (continuous_schwartz_multiplier_circle
      (torusHeatDerivativeProfile (if j = i then M else 0)) ha).comp (continuous_apply j)
  have hc : ‖(a : ℂ) ^ (2 * M)‖ₑ = ENNReal.ofReal (a ^ (2 * M)) := by
    rw [← ofReal_norm, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  simp only [torusWeightedHeatKernel, enorm_mul]
  rw [lintegral_const_mul _ hm, hc, ENNReal.ofReal_mul hC]
  exact (mul_le_mul' le_rfl (hb a ha)).trans_eq (mul_comm _ _)

theorem lintegral_torusWeightedHeatKernel_time_bound (M : ℕ) (i : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 < s →
      (∫⁻ x : Torus3, ‖torusWeightedHeatKernel M i (Real.sqrt s)⁻¹ x‖ₑ) ≤
        ENNReal.ofReal (C * s ^ (-(M : ℝ))) := by
  obtain ⟨C, hC, hb⟩ := lintegral_torusWeightedHeatKernel_bound_uniform M i
  refine ⟨C, hC, fun s hs => ?_⟩
  have he : ((Real.sqrt s)⁻¹) ^ (2 * M) = s ^ (-(M : ℝ)) := by
    rw [Real.rpow_neg hs.le, Real.rpow_natCast, inv_pow, pow_mul, Real.sq_sqrt hs.le]
  simpa only [he] using hb (Real.sqrt s)⁻¹ (inv_pos.mpr (Real.sqrt_pos.mpr hs))

theorem mFourierCoeff_torusWeightedHeatKernel (M : ℕ) (i : Fin 3) {a : ℝ}
    (ha : 0 < a) (k : Fin 3 → ℤ) :
    UnitAddTorus.mFourierCoeff (torusWeightedHeatKernel M i a) k =
      (a : ℂ) ^ (2 * M) * ∏ j : Fin 3,
        torusHeatDerivativeProfile (if j = i then M else 0) ((k j : ℝ) / a) := by
  rw [torus_mFourierCoeff_eq_volume_integral]
  calc
    _ = (a : ℂ) ^ (2 * M) * ∫ x : Torus3, UnitAddTorus.mFourier (-k) x *
        (∏ j : Fin 3, ∑' l : ℤ,
          torusHeatDerivativeProfile (if j = i then M else 0) ((l : ℝ) / a) * fourier l (x j)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp [torusWeightedHeatKernel]
      ring
    _ = _ := by
      rw [← torus_mFourierCoeff_eq_volume_integral,
        mFourierCoeff_schwartz_tensor_multiplier _ ha]

theorem mFourierCoeff_torusWeightedHeatKernel_time (M : ℕ) (i : Fin 3)
    {s : ℝ} (hs : 0 < s) (k : Fin 3 → ℤ) :
    UnitAddTorus.mFourierCoeff (torusWeightedHeatKernel M i (Real.sqrt s)⁻¹) k =
      (k i : ℂ) ^ (2 * M) * ∏ j : Fin 3,
        ((Real.exp (-4 * Real.pi ^ 2 * s * (k j : ℝ) ^ 2) : ℝ) : ℂ) := by
  classical
  rw [mFourierCoeff_torusWeightedHeatKernel M i (inv_pos.mpr (Real.sqrt_pos.mpr hs))]
  simp only [torusHeatDerivativeProfile_apply, Finset.prod_mul_distrib]
  have hprod : (∏ j : Fin 3,
      (((k j : ℝ) / (Real.sqrt s)⁻¹ : ℝ) : ℂ) ^ (2 * if j = i then M else 0)) =
      (((k i : ℝ) / (Real.sqrt s)⁻¹ : ℝ) : ℂ) ^ (2 * M) := by
    calc
      _ = (((k i : ℝ) / (Real.sqrt s)⁻¹ : ℝ) : ℂ) ^ (2 * if i = i then M else 0) := by
        apply Finset.prod_eq_single i
        · intro j _ hj
          rw [ite_eq_right hj, mul_zero, pow_zero]
        · intro hi
          exact False.elim (hi (Finset.mem_univ i))
      _ = _ := by rw [ite_eq_left rfl]
  rw [hprod, ← mul_assoc]
  have hpoly : (((Real.sqrt s)⁻¹ : ℝ) : ℂ) ^ (2 * M) *
      (((k i : ℝ) / (Real.sqrt s)⁻¹ : ℝ) : ℂ) ^ (2 * M) = (k i : ℂ) ^ (2 * M) := by
    rw [← mul_pow]
    congr 1
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hs).ne']
  rw [hpoly]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  have he : -(4 * Real.pi ^ 2 * ((k j : ℝ) / (Real.sqrt s)⁻¹) ^ 2) =
      -4 * Real.pi ^ 2 * s * (k j : ℝ) ^ 2 := by
    rw [div_inv_eq_mul, mul_pow, Real.sq_sqrt hs.le]
    ring
  rw [he]

end RegularityStructures

end
