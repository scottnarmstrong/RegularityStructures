/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HolderBesovFourierReconstruction
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Heat-regularised dyadic reconstruction

The complex heat operator acts diagonally on the torus characters. Applying it to the finite dyadic
telescoping identity and then using absolute Fourier summability reconstructs the heat
regularisation in the uniform norm. This is the reconstruction step in the equivalence of the heat
norm (2.3) of the statement with the Littlewood--Paley norm. No annular heat-decay bound is assumed.
-/

public noncomputable section

open MeasureTheory UnitAddTorus Filter Real
open scoped Topology

namespace RegularityStructures

private theorem heatOp_complex_gauss {s : ℝ} (hs : 0 < s)
    (g : C(Torus3, ℂ)) (x : Torus3) :
    PDE.heatOp s g x = ∫ y : Fin 3 → ℝ, (gaussKernel s y : ℂ) * g (x - torusProj y) := by
  let F : (Fin 3 → ℝ) → ℂ := fun y => (gaussKernel s y : ℂ) * g (x - torusProj y)
  have h1 : PDE.heatOp s g x = (√s ^ 3) • ∫ z, F (√s • z) := by
    rw [PDE.heatOp_apply, ← integral_smul]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [PDE.gaussKernel_one_eq hs]
    dsimp [F]
    simp only [Complex.ofReal_mul]
    ring
  have hst : 0 < √s := sqrt_pos.mpr hs
  rw [h1, Measure.integral_comp_smul, Module.finrank_fin_fun, smul_smul,
    abs_of_pos (inv_pos.mpr (pow_pos hst _)),
    mul_inv_cancel₀ (pow_ne_zero _ hst.ne'), one_smul]

private theorem character_space_sub (k : Fin 3 → ℤ) (x y : Torus3) :
    mFourier k (x - y) = mFourier k x * mFourier (-k) y := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, Pi.neg_apply,
    fourier_apply, sub_eq_add_neg, zsmul_add, zsmul_neg, neg_zsmul,
    AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

theorem heatOp_mFourier {s : ℝ} (hs : 0 < s) (k : Fin 3 → ℤ) :
    PDE.heatOp s (mFourier k) =
      (∏ i : Fin 3, Complex.exp ((-4 * π ^ 2 * s * (k i : ℝ) ^ 2 : ℝ) : ℂ)) •
        mFourier k := by
  ext x
  rw [heatOp_complex_gauss hs]
  simp_rw [character_space_sub]
  calc
    _ = (∫ y : Fin 3 → ℝ, (gaussKernel s y : ℂ) * mFourier (-k) (torusProj y)) *
        mFourier k x := by
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [] with y
      ring
    _ = _ := by
      rw [integral_gaussKernel_mul_fourierCharacter hs]
      simp only [Pi.neg_apply, Int.cast_neg, neg_sq, ContinuousMap.smul_apply, smul_eq_mul]

private theorem heatOp_complex_smul (s : ℝ) (c : ℂ) (g : C(Torus3, ℂ)) :
    PDE.heatOp s (c • g) = c • PDE.heatOp s g := by
  ext x
  simp only [PDE.heatOp_apply, ContinuousMap.smul_apply]
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with y
  exact smul_comm _ _ _

private theorem heatOp_sum {ι : Type*} (s : ℝ) (S : Finset ι) (g : ι → C(Torus3, ℂ)) :
    PDE.heatOp s (∑ j ∈ S, g j) = ∑ j ∈ S, PDE.heatOp s (g j) :=
  map_sum (PDE.heatOpCLM (E := ℂ) s) g S

theorem tendsto_sum_heatOp_torusLittlewoodPaleyBlock {s : ℝ} (hs : 0 < s)
    (f : C(Torus3, ℝ)) :
    Tendsto (fun n : ℕ => ∑ j ∈ Finset.range (n + 1),
      PDE.heatOp s (torusLittlewoodPaleyBlock j f)) atTop
      (𝓝 (⟨fun x : Torus3 => (PDE.heatOp s f x : ℂ),
        Complex.continuous_ofReal.comp (PDE.heatOp s f).continuous⟩ : C(Torus3, ℂ))) := by
  let g : C(Torus3, ℂ) :=
    ⟨fun x => (PDE.heatOp s f x : ℂ), Complex.continuous_ofReal.comp (PDE.heatOp s f).continuous⟩
  have h := tendsto_torusLowFrequency_sum_of_summable g (summable_mFourierCoeff_heatOp hs f)
  have hcoef (k : Fin 3 → ℤ) : mFourierCoeff g k =
      (∏ i : Fin 3, Complex.exp ((-4 * π ^ 2 * s * (k i : ℝ) ^ 2 : ℝ) : ℂ)) *
        mFourierCoeff (fun x : Torus3 => (f x : ℂ)) k := by
    change mFourierCoeff (fun x : Torus3 => (PDE.heatOp s f x : ℂ)) k = _
    simp_rw [PDE.heatOp_eq_heatSemigroup hs]
    exact mFourierCoeff_heatSemigroup hs f k
  have he (n : ℕ) :
      (∑ j ∈ Finset.range (n + 1), PDE.heatOp s (torusLittlewoodPaleyBlock j f)) =
      ∑ k ∈ torusLPFrequencyBox n,
        ((torusLowFrequencySymbol n k : ℂ) * mFourierCoeff g k) • mFourier k := by
    rw [← heatOp_sum]
    have htel : (∑ j ∈ Finset.range (n + 1), torusLittlewoodPaleyBlock j f) =
        ∑ k ∈ torusLPFrequencyBox n,
          ((torusLowFrequencySymbol n k : ℂ) *
            mFourierCoeff (fun x : Torus3 => (f x : ℂ)) k) • mFourier k := by
      ext x
      simpa only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul] using
        sum_torusLittlewoodPaleyBlock_apply n f x
    rw [htel, heatOp_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [heatOp_complex_smul, heatOp_mFourier hs, smul_smul, hcoef]
    congr 1
    ring
  simpa only [he] using h

end RegularityStructures

end

