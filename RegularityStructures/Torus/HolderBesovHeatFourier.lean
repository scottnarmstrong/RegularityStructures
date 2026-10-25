/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HolderBesovGaussianCharacter
public import Mathlib.MeasureTheory.Group.Integral
import RegularityStructures.Torus.HeatKernelFacts
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Fourier coefficients of the heat semigroup

Fubini and translation of Fourier characters compute the multiplier directly from the Euclidean
convolution defining `heatSemigroup`; no replacement semigroup is introduced. This is the Fourier
identity used in the equivalence of the heat norm (2.3) of the statement with the Littlewood--Paley
norm.
-/

public noncomputable section

open MeasureTheory UnitAddTorus

namespace RegularityStructures

theorem torus_mFourierCoeff_eq_volume_integral (g : Torus3 → ℂ) (k : Fin 3 → ℤ) :
    mFourierCoeff g k = ∫ x : Torus3, mFourier (-k) x * g x := by
  simp only [mFourierCoeff, smul_eq_mul, MeasureSpace.volume,
    AddCircle.haarAddCircle, ENNReal.ofReal_one, one_smul]

private theorem character_space_add (k : Fin 3 → ℤ) (x y : Torus3) :
    mFourier k (x + y) = mFourier k x * mFourier k y := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply,
    zsmul_add, AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

private theorem character_point_norm (k : Fin 3 → ℤ) (x : Torus3) :
    ‖mFourier k x‖ = 1 := by
  simp only [mFourier, ContinuousMap.coe_mk, norm_prod, fourier_apply,
    Circle.norm_coe, Finset.prod_const_one]

theorem torus_mFourierCoeff_translate (f : C(Torus3, ℝ)) (k : Fin 3 → ℤ) (a : Torus3) :
    (∫ x : Torus3, mFourier (-k) x * (f (x - a) : ℂ)) =
      mFourier (-k) a * mFourierCoeff (fun x : Torus3 => (f x : ℂ)) k := by
  rw [torus_mFourierCoeff_eq_volume_integral]
  calc
    _ = ∫ x : Torus3, mFourier (-k) (x + a) * (f x : ℂ) := by
      simpa only [add_sub_cancel_right] using
        (integral_add_right_eq_self
          (fun x : Torus3 => mFourier (-k) x * (f (x - a) : ℂ)) a).symm
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [character_space_add]
      ring

theorem mFourierCoeff_heatSemigroup {s : ℝ} (hs : 0 < s) (f : C(Torus3, ℝ))
    (k : Fin 3 → ℤ) :
    mFourierCoeff (fun x : Torus3 => (heatSemigroup s f x : ℂ)) k =
      (∏ i : Fin 3, Complex.exp ((-4 * Real.pi ^ 2 * s * (k i : ℝ) ^ 2 : ℝ) : ℂ)) *
        mFourierCoeff (fun x : Torus3 => (f x : ℂ)) k := by
  let F : Torus3 × (Fin 3 → ℝ) → ℂ := fun q =>
    (gaussKernel s q.2 : ℂ) * (mFourier (-k) q.1 * (f (q.1 - torusProj q.2) : ℂ))
  have hproj : Continuous torusProj := by
    unfold torusProj
    fun_prop
  have hFc : Continuous F :=
    (Complex.continuous_ofReal.comp ((continuous_gaussKernel_fixed hs).comp continuous_snd)).mul
      (((mFourier (-k)).continuous.comp continuous_fst).mul
        (Complex.continuous_ofReal.comp (f.continuous.comp
          (continuous_fst.sub (hproj.comp continuous_snd)))))
  have hFi : Integrable F ((volume : Measure Torus3).prod volume) := by
    apply (((integrable_gaussKernel hs).norm.comp_snd (volume : Measure Torus3)).mul_const
      ‖f‖).mono' hFc.aestronglyMeasurable
    filter_upwards [] with q
    change ‖(gaussKernel s q.2 : ℂ) *
      (mFourier (-k) q.1 * (f (q.1 - torusProj q.2) : ℂ))‖ ≤ ‖gaussKernel s q.2‖ * ‖f‖
    rw [norm_mul, norm_mul, character_point_norm, one_mul, Complex.norm_real, Complex.norm_real]
    exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (norm_nonneg _)
  rw [torus_mFourierCoeff_eq_volume_integral]
  calc
    _ = ∫ x : Torus3, ∫ y : Fin 3 → ℝ, F (x, y) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [heatSemigroup, ← integral_complex_ofReal, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      dsimp [F]
      push_cast
      ring
    _ = ∫ y : Fin 3 → ℝ, ∫ x : Torus3, F (x, y) := integral_integral_swap hFi
    _ = ∫ y : Fin 3 → ℝ, ((gaussKernel s y : ℂ) * mFourier (-k) (torusProj y)) *
        mFourierCoeff (fun x : Torus3 => (f x : ℂ)) k := by
      apply integral_congr_ae
      filter_upwards [] with y
      change (∫ x : Torus3, (gaussKernel s y : ℂ) *
        (mFourier (-k) x * (f (x - torusProj y) : ℂ))) = _
      rw [integral_const_mul, torus_mFourierCoeff_translate]
      ring
    _ = (∫ y : Fin 3 → ℝ, (gaussKernel s y : ℂ) * mFourier (-k) (torusProj y)) *
        mFourierCoeff (fun x : Torus3 => (f x : ℂ)) k := integral_mul_const _ _
    _ = _ := by
      rw [integral_gaussKernel_mul_fourierCharacter hs]
      simp only [Pi.neg_apply, Int.cast_neg, neg_sq]

end RegularityStructures

end
