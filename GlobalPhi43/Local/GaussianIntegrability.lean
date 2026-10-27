/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.GaussianJointTime

/-! Integrability needed when separating the time and Laplacian terms. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures RegularityStructures.PDE MeasureTheory Real

 theorem integrable_gaussian_bounded {g : (Fin 3 → ℝ) → ℝ} {B : ℝ}
    (hg : Continuous g) (hB : ∀ z, |g z| ≤ B) :
    Integrable (fun z : Fin 3 → ℝ => gaussKernel 1 z * g z) := by
  apply (integrable_gaussKernel_one.mul_const B).mono' (by fun_prop : Continuous _).aestronglyMeasurable
  apply ae_of_all
  intro z
  rw [norm_mul, Real.norm_of_nonneg (gaussKernel_one_nonneg z), Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hB z) (gaussKernel_one_nonneg z)

 theorem integrable_gaussian_gradient {ψ : (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] ℝ}
    (hψ : Continuous ψ) {C t : ℝ} (hC : ∀ w, ‖ψ w‖ ≤ C) (ht : 0 < t) (y : Fin 3 → ℝ) :
    Integrable (fun z : Fin 3 → ℝ => gaussKernel 1 z * ψ (y - √t • z) (-(2 * √t)⁻¹ • z)) := by
  apply (integrable_norm_mul_gaussKernel_one.const_mul (C * (2 * √t)⁻¹)).mono'
    (by fun_prop : Continuous _).aestronglyMeasurable
  apply ae_of_all
  intro z
  rw [norm_mul, Real.norm_of_nonneg (gaussKernel_one_nonneg z)]
  have hn : ‖-(2 * √t)⁻¹ • z‖ = (2 * √t)⁻¹ * ‖z‖ := by
    rw [norm_smul, norm_neg, Real.norm_of_nonneg (by positivity)]
  have hb := ((ψ (y - √t • z)).le_opNorm (-(2 * √t)⁻¹ • z)).trans
    (mul_le_mul_of_nonneg_right (hC (y - √t • z)) (norm_nonneg _))
  rw [hn] at hb
  nlinarith [mul_le_mul_of_nonneg_left hb (gaussKernel_one_nonneg z)]

 theorem integrable_gaussian_laplacian
    {H : (Fin 3 → ℝ) → (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) →L[ℝ] ℝ}
    (hH : Continuous H) {C : ℝ} (hC : ∀ w, ‖H w‖ ≤ C) (t : ℝ) (y : Fin 3 → ℝ) :
    Integrable (fun z : Fin 3 → ℝ => gaussKernel 1 z *
      ∑ i : Fin 3, H (y - √t • z) (Pi.single i 1) (Pi.single i 1)) := by
  apply integrable_gaussian_bounded (by fun_prop)
  intro z
  calc
    |∑ i : Fin 3, H (y - √t • z) (Pi.single i 1) (Pi.single i 1)| ≤
        ∑ i : Fin 3, |H (y - √t • z) (Pi.single i 1) (Pi.single i 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3, C * ‖(Pi.single i 1 : Fin 3 → ℝ)‖ * ‖(Pi.single i 1 : Fin 3 → ℝ)‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [← Real.norm_eq_abs]
      exact ((H _ _).le_opNorm _).trans (mul_le_mul_of_nonneg_right
        (((H _).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC (y - √t • z)) (norm_nonneg _))) (norm_nonneg _))

end GlobalPhi43.Local
