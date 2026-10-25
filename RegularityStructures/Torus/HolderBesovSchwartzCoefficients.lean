/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HolderBesovPoissonKernel
public import RegularityStructures.Torus.HolderBesovHeatFourier
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Fourier coefficients of the actual periodic Schwartz multipliers

Absolute summability justifies integration of the Fourier series, so its coefficient at `k` is
exactly the sampled profile value `m(k/a)`. Tensorisation gives the corresponding identity on the
three-torus. These identify the weighted heat kernels used in the equivalence of the heat norm (2.3)
of the statement with the Littlewood--Paley norm.
-/

public noncomputable section

open MeasureTheory UnitAddTorus
open scoped SchwartzMap

namespace RegularityStructures

private theorem character_point_norm (k : ℤ) (x : UnitAddCircle) : ‖fourier k x‖ = 1 := by
  rw [fourier_apply]
  exact Circle.norm_coe _

theorem integral_schwartz_multiplier_circle_character (m : 𝓢(ℝ, ℂ))
    {a : ℝ} (ha : 0 < a) (l : ℤ) :
    (∫ x : UnitAddCircle, fourier (-l) x *
      (∑' k : ℤ, m ((k : ℝ) / a) * fourier k x)) = m ((l : ℝ) / a) := by
  classical
  have hv : (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp only [ENNReal.ofReal_one, one_smul]
  let : IsProbabilityMeasure (volume : Measure UnitAddCircle) := by
    rw [hv]
    infer_instance
  let F : ℤ → UnitAddCircle → ℂ := fun k x =>
    m ((k : ℝ) / a) * (fourier (-l) x * fourier k x)
  have hnorm (k : ℤ) (x : UnitAddCircle) : ‖F k x‖ = ‖m ((k : ℝ) / a)‖ := by
    simp only [F, norm_mul, character_point_norm, mul_one]
  have hFi (k : ℤ) : Integrable (F k) :=
    (((fourier (-l)).continuous.mul (fourier k).continuous).const_mul _).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsum : Summable (fun k : ℤ => ∫ x : UnitAddCircle, ‖F k x‖) := by
    simp_rw [hnorm]
    simpa only [integral_const, probReal_univ, one_smul] using (summable_schwartz_dilated_int m ha).norm
  have horth (k : ℤ) : (∫ x : UnitAddCircle, fourier (-l) x * fourier k x) =
      (Pi.single k (1 : ℂ) : ℤ → ℂ) l := by
    have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) k) l
    simpa only [fourierCoeff, smul_eq_mul, ← hv] using h
  calc
    _ = ∫ x : UnitAddCircle, ∑' k : ℤ, F k x := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      dsimp [F]
      ring
    _ = ∑' k : ℤ, ∫ x : UnitAddCircle, F k x :=
      (integral_tsum_of_summable_integral_norm hFi hsum).symm
    _ = ∑' k : ℤ, m ((k : ℝ) / a) * (Pi.single k (1 : ℂ) : ℤ → ℂ) l := by
      apply tsum_congr
      intro k
      rw [show (∫ x : UnitAddCircle, F k x) = m ((k : ℝ) / a) *
        ∫ x : UnitAddCircle, fourier (-l) x * fourier k x from integral_const_mul _ _, horth]
    _ = _ := by simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, tsum_ite_eq']

theorem mFourierCoeff_schwartz_tensor_multiplier (m : Fin 3 → 𝓢(ℝ, ℂ))
    {a : ℝ} (ha : 0 < a) (k : Fin 3 → ℤ) :
    mFourierCoeff (fun x : Torus3 => ∏ j : Fin 3,
      ∑' l : ℤ, m j ((l : ℝ) / a) * fourier l (x j)) k =
      ∏ j : Fin 3, m j ((k j : ℝ) / a) := by
  rw [torus_mFourierCoeff_eq_volume_integral]
  simp only [mFourier, ContinuousMap.coe_mk, Pi.neg_apply, ← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_volume_eq_prod (fun j : Fin 3 => fun x : UnitAddCircle =>
    fourier (-(k j)) x * (∑' l : ℤ, m j ((l : ℝ) / a) * fourier l x))]
  exact Finset.prod_congr rfl fun j _ => integral_schwartz_multiplier_circle_character (m j) ha (k j)

end RegularityStructures

end
