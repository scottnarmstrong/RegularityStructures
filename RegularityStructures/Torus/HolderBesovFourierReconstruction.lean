/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HolderBesovFrequencyGeometry
public import RegularityStructures.Torus.HolderBesovHeatFourier
public import RegularityStructures.PDE.HeatOpBridge
import RegularityStructures.Torus.HeatKernelIntegral
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Reconstruction by the actual low-frequency cutoffs

For summable Fourier coefficients, dominated convergence identifies the cutoff limit in the uniform
norm. The heat multiplier gives this summability for every positive-time regularisation of a
continuous input. These facts are reconstruction inputs to the equivalence of the heat norm (2.3) of
the statement with the Littlewood--Paley norm.
-/

public noncomputable section

open MeasureTheory UnitAddTorus Filter
open scoped Topology

namespace RegularityStructures

private theorem character_point_norm (k : Fin 3 → ℤ) (x : Torus3) :
    ‖mFourier k x‖ = 1 := by
  simp only [mFourier, ContinuousMap.coe_mk, norm_prod, fourier_apply,
    Circle.norm_coe, Finset.prod_const_one]

theorem norm_torus_mFourierCoeff_le (f : C(Torus3, ℝ)) (k : Fin 3 → ℤ) :
    ‖mFourierCoeff (fun x : Torus3 => (f x : ℂ)) k‖ ≤ ‖f‖ := by
  rw [torus_mFourierCoeff_eq_volume_integral]
  have hb : ∀ᵐ x : Torus3, ‖mFourier (-k) x * (f x : ℂ)‖ ≤ ‖f‖ := by
    filter_upwards [] with x
    rw [norm_mul, character_point_norm, one_mul, Complex.norm_real]
    exact f.norm_coe_le_norm x
  have hv : (volume : Measure Torus3) Set.univ = 1 := by
    change (Measure.pi (fun _ : Fin 3 => (volume : Measure UnitAddCircle))) Set.univ = 1
    rw [Measure.pi_univ]
    simp only [AddCircle.measure_univ, ENNReal.ofReal_one, Finset.prod_const_one]
  simpa only [measureReal_def, hv, ENNReal.toReal_one, mul_one] using
    norm_integral_le_of_norm_le_const hb

theorem summable_torus_heat_multiplier {s : ℝ} (hs : 0 < s) :
    Summable (fun k : Fin 3 → ℤ =>
      ∏ i : Fin 3, Real.exp (-4 * Real.pi ^ 2 * s * (k i : ℝ) ^ 2)) := by
  have ht : 0 < (16 * Real.pi ^ 2 * s)⁻¹ :=
    inv_pos.mpr (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos Real.pi_pos)) hs)
  have h := summable_gaussian_vector ht (0 : Fin 3 → ℝ)
    (fun _ => ⟨le_rfl, zero_lt_one⟩)
  have he : (4 * (16 * Real.pi ^ 2 * s)⁻¹)⁻¹ = 4 * Real.pi ^ 2 * s := by
    field_simp
    ring
  simpa only [Pi.zero_apply, zero_add, he, neg_mul] using h

theorem summable_mFourierCoeff_heatOp {s : ℝ} (hs : 0 < s) (f : C(Torus3, ℝ)) :
    Summable (mFourierCoeff (fun x : Torus3 => (PDE.heatOp s f x : ℂ))) := by
  apply ((summable_torus_heat_multiplier hs).mul_right ‖f‖).of_norm_bounded
  intro k
  have he : mFourierCoeff (fun x : Torus3 => (PDE.heatOp s f x : ℂ)) k =
      (∏ i : Fin 3, Complex.exp ((-4 * Real.pi ^ 2 * s * (k i : ℝ) ^ 2 : ℝ) : ℂ)) *
        mFourierCoeff (fun x : Torus3 => (f x : ℂ)) k := by
    simp_rw [PDE.heatOp_eq_heatSemigroup hs]
    exact mFourierCoeff_heatSemigroup hs f k
  rw [he, norm_mul]
  simp only [norm_prod, Complex.norm_exp, Complex.ofReal_re]
  exact mul_le_mul_of_nonneg_left (norm_torus_mFourierCoeff_le f k)
    (Finset.prod_nonneg fun _ _ => Real.exp_nonneg _)

theorem tendsto_torusLowFrequency_sum_of_summable (g : C(Torus3, ℂ))
    (hg : Summable (mFourierCoeff g)) :
    Tendsto (fun n : ℕ => ∑ k ∈ torusLPFrequencyBox n,
      ((torusLowFrequencySymbol n k : ℂ) * mFourierCoeff g k) • mFourier k)
        atTop (𝓝 g) := by
  let F : ℕ → (Fin 3 → ℤ) → C(Torus3, ℂ) := fun n k =>
    ((torusLowFrequencySymbol n k : ℂ) * mFourierCoeff g k) • mFourier k
  have hlim (k : Fin 3 → ℤ) : Tendsto (fun n => F n k) atTop
      (𝓝 (mFourierCoeff g k • mFourier k)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [torusLowFrequencySymbol_eventually_eq_one k] with n hn
    simp only [F, hn, Complex.ofReal_one, one_mul]
  have hbound : ∀ᶠ n : ℕ in atTop, ∀ k : Fin 3 → ℤ, ‖F n k‖ ≤ ‖mFourierCoeff g k‖ := by
    filter_upwards [] with n k
    simp only [F, norm_smul, norm_mul, mFourier_norm, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (torusLowFrequencySymbol_nonneg n k)]
    exact mul_le_of_le_one_left (norm_nonneg _) (torusLowFrequencySymbol_le_one n k)
  have h := tendsto_tsum_of_dominated_convergence hg.norm hlim hbound
  rw [(hasSum_mFourier_series_of_summable hg).tsum_eq] at h
  convert h using 1
  funext n
  symm
  apply tsum_eq_sum
  intro k hk
  simp only [F, torusLowFrequencySymbol_eq_zero_of_notMem_box n k hk,
    Complex.ofReal_zero, zero_mul]
  ext x
  change (0 : ℂ) * mFourier k x = 0
  exact zero_mul _

end RegularityStructures

end
