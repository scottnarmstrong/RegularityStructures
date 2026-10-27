/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.GaussianIntegrability
public import GlobalPhi43.Local.CompactSpatialSlice

/-! The joint space-time Gaussian derivative is the average of time
plus Laplacian. All bounds follow from actual compact smooth input. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures RegularityStructures.PDE MeasureTheory Real
open scoped ContDiff

 theorem hasDerivAt_gaussian_joint_heat {φ : ParabolicSpace → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hcomp : HasCompactSupport φ)
    {t : ℝ} (ht : 0 < t) (y : Fin 3 → ℝ) :
    HasDerivAt (fun s => ∫ z : Fin 3 → ℝ, gaussKernel 1 z * φ (s, y - √s • z))
      (∫ z : Fin 3 → ℝ, gaussKernel 1 z *
        (fderiv ℝ φ (t, y - √t • z) (1, 0) + ∑ i : Fin 3,
          fderiv ℝ (fderiv ℝ (fun w : Fin 3 → ℝ => φ (t, w)))
            (y - √t • z) (Pi.single i 1) (Pi.single i 1))) t := by
  have hdc := hφ.continuous_fderiv (by simp)
  obtain ⟨B, hB⟩ := hφ.continuous.bounded_above_of_compact_support hcomp
  obtain ⟨C, hC⟩ := hdc.bounded_above_of_compact_support (hcomp.fderiv ℝ)
  have hD := hasDerivAt_gaussian_joint_average
    (fun p => (hφ.differentiable (by simp) p).hasFDerivAt) hdc
    (by simpa only [Real.norm_eq_abs] using hB) hC ht y
  let g : (Fin 3 → ℝ) → ℝ := fun w => φ (t, w)
  have hgc : ContDiff ℝ ∞ g := smooth_spatial_slice hφ t
  have hgcomp : HasCompactSupport g := compact_spatial_slice hcomp t
  have hdg : ContDiff ℝ ∞ (fderiv ℝ g) := hgc.fderiv_right (by simp)
  obtain ⟨C₁, hC₁⟩ := hdg.continuous.bounded_above_of_compact_support (hgcomp.fderiv ℝ)
  obtain ⟨C₂, hC₂⟩ := (hdg.continuous_fderiv (by simp)).bounded_above_of_compact_support
    ((hgcomp.fderiv ℝ).fderiv ℝ)
  have hiT : Integrable (fun z : Fin 3 → ℝ => gaussKernel 1 z *
      fderiv ℝ φ (t, y - √t • z) (1, 0)) := by
    apply integrable_gaussian_bounded (by fun_prop)
    intro z
    rw [← Real.norm_eq_abs]
    exact ((fderiv ℝ φ _).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))
  have hiG := integrable_gaussian_gradient hdg.continuous hC₁ ht y
  have hiL := integrable_gaussian_laplacian (hdg.continuous_fderiv (by simp)) hC₂ t y
  have hIBP := integral_gaussKernel_smul_deriv_eq
    (fun w => (hdg.differentiable (by simp) w).hasFDerivAt)
    (hdg.continuous_fderiv (by simp)) hC₁ hC₂ y ht
  simp only [smul_eq_mul] at hIBP
  have hspatial (w v : Fin 3 → ℝ) :
      fderiv ℝ g w v = fderiv ℝ φ (t, w) (0, v) := by
    have hh := congrArg (fun L : (Fin 3 → ℝ) →L[ℝ] ℝ => L v)
      (spatial_slice_fderiv (hφ.differentiable (by simp)) t w)
    simpa only [g, ContinuousLinearMap.comp_apply, heatSpatialInsert,
      ContinuousLinearMap.prod_apply, zero_apply,
      ContinuousLinearMap.id_apply] using hh
  have hsplit : (∫ z : Fin 3 → ℝ, gaussKernel 1 z *
      fderiv ℝ φ (t, y - √t • z) (1, -(2 * √t)⁻¹ • z)) =
      (∫ z : Fin 3 → ℝ, gaussKernel 1 z * fderiv ℝ φ (t, y - √t • z) (1, 0)) +
      (∫ z : Fin 3 → ℝ, gaussKernel 1 z * fderiv ℝ g (y - √t • z) (-(2 * √t)⁻¹ • z)) := by
    rw [← integral_add hiT hiG]
    apply integral_congr_ae
    apply ae_of_all
    intro z
    dsimp only
    rw [hspatial]
    have he : ((1 : ℝ), -(2 * √t)⁻¹ • z) = (1, 0) + (0, -(2 * √t)⁻¹ • z) := by
      ext <;> simp
    rw [he, map_add, mul_add]
  rw [hsplit, hIBP] at hD
  have heq : (∫ z : Fin 3 → ℝ, gaussKernel 1 z *
      (fderiv ℝ φ (t, y - √t • z) (1, 0) + ∑ i : Fin 3,
        fderiv ℝ (fderiv ℝ g) (y - √t • z) (Pi.single i 1) (Pi.single i 1))) =
      (∫ z : Fin 3 → ℝ, gaussKernel 1 z * fderiv ℝ φ (t, y - √t • z) (1, 0)) +
      (∫ z : Fin 3 → ℝ, gaussKernel 1 z * ∑ i : Fin 3,
        fderiv ℝ (fderiv ℝ g) (y - √t • z) (Pi.single i 1) (Pi.single i 1)) := by
    simp_rw [mul_add]
    exact integral_add hiT hiL
  rw [← heq] at hD
  exact hD

end GlobalPhi43.Local
