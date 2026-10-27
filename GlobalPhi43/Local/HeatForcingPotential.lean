/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.HeatKernelFundamentalIdentity

/-! Actual Gaussian mass bounds the ordinary-heat forcing potential.
All measurability/integrability follows from the compact continuous test. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures RegularityStructures.PDE MeasureTheory Set Real

 theorem heat_forcing_potential_bound {φ : ParabolicSpace → ℝ}
    (hφ : Continuous φ) (hcomp : HasCompactSupport φ) (y : Fin 3 → ℝ)
    {T F : ℝ} (hT : 0 ≤ T) (hF : ∀ s ∈ Ioc (0 : ℝ) T, ∀ z : Fin 3 → ℝ, |φ (s, z)| ≤ F) :
    IntervalIntegrable (fun s => ∫ w : Fin 3 → ℝ, heatKernelR4 (s, w) * φ (s, y - w)) volume 0 T ∧
      |∫ s in (0 : ℝ)..T, ∫ w : Fin 3 → ℝ, heatKernelR4 (s, w) * φ (s, y - w)| ≤ T * F := by
  have hc := continuous_gaussian_joint_average hφ hcomp y
  have heq (s : ℝ) (hs : 0 < s) :
      (∫ z : Fin 3 → ℝ, gaussKernel 1 z * φ (s, y - √s • z)) =
        ∫ w : Fin 3 → ℝ, heatKernelR4 (s, w) * φ (s, y - w) :=
    gaussian_change_variables hs (fun w : Fin 3 → ℝ => φ (s, y - w))
  constructor
  · apply (hc.intervalIntegrable 0 T).congr_uIoo
    intro s hs
    rw [uIoo_of_le hT] at hs
    exact heq s hs.1
  · have hinner (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) T) :
        |∫ w : Fin 3 → ℝ, heatKernelR4 (s, w) * φ (s, y - w)| ≤ F := by
      rw [← heq s hs.1]
      have hpoint (z : Fin 3 → ℝ) : ‖gaussKernel 1 z * φ (s, y - √s • z)‖ ≤ gaussKernel 1 z * F := by
        rw [norm_mul, Real.norm_of_nonneg (gaussKernel_one_nonneg z), Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hF s hs _) (gaussKernel_one_nonneg z)
      have hb := norm_integral_le_of_norm_le (integrable_gaussKernel_one.mul_const F) (ae_of_all _ hpoint)
      simpa only [Real.norm_eq_abs, integral_mul_const,
        integral_gaussKernel (by norm_num : (0 : ℝ) < 1), one_mul] using hb
    have hout := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := T)
      (f := fun s => ∫ w : Fin 3 → ℝ, heatKernelR4 (s, w) * φ (s, y - w)) (C := F)
      (fun s hs => by
        rw [uIoc_of_le hT] at hs
        simpa only [Real.norm_eq_abs] using hinner s hs)
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hT, mul_comm] using hout

end GlobalPhi43.Local
