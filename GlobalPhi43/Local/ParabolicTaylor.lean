/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.SpatialQuadraticTaylor
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-! The parabolic Taylor step, including the one-sided terminal time face. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures Set Metric

/-- Uniform time-derivative and spatial-Hessian bounds yield a spatially
affine error of order R² on a past box. No future-time neighbourhood is used
by either mean-value estimate. -/
theorem parabolic_quadratic_taylor (h : ParabolicSpace → ℝ) (x y : ParabolicSpace)
    {R S : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S) (hy : y ∈ pastBall x R)
    (ht : ∀ t ∈ Icc (x.1 - R ^ 2) x.1, DifferentiableAt ℝ (fun s => h (s, y.2)) t)
    (hdt : ∀ t ∈ Icc (x.1 - R ^ 2) x.1, |deriv (fun s => h (s, y.2)) t| ≤ S)
    (hg : ∀ z ∈ closedBall x.2 R, DifferentiableAt ℝ (fun w => h (x.1, w)) z)
    (hD : ∀ z ∈ closedBall x.2 R,
      DifferentiableAt ℝ (fderiv ℝ (fun w => h (x.1, w))) z)
    (hDD : ∀ z ∈ closedBall x.2 R,
      ‖fderiv ℝ (fderiv ℝ (fun w => h (x.1, w))) z‖ ≤ S) :
    |h y - h x - fderiv ℝ (fun w => h (x.1, w)) x.2 (y.2 - x.2)| ≤ 2 * S * R ^ 2 := by
  have htime : |x.1 - y.1| ≤ R ^ 2 :=
    ((Real.sqrt_le_left hR).mp ((le_max_left _ _).trans hy.1.le))
  have hytime : y.1 ∈ Icc (x.1 - R ^ 2) x.1 := by
    have hh := le_abs_self (x.1 - y.1)
    exact ⟨by linarith, hy.2.le⟩
  have hxtime : x.1 ∈ Icc (x.1 - R ^ 2) x.1 := ⟨by nlinarith [sq_nonneg R], le_rfl⟩
  have htbound : |h (y.1, y.2) - h (x.1, y.2)| ≤ S * R ^ 2 := by
    have hb := (convex_Icc (x.1 - R ^ 2) x.1).norm_image_sub_le_of_norm_fderiv_le ht
      (fun t ht' => by simpa only [← norm_deriv_eq_norm_fderiv, Real.norm_eq_abs] using hdt t ht')
      hxtime hytime
    have hb' : |h (y.1, y.2) - h (x.1, y.2)| ≤ S * |x.1 - y.1| := by
      simpa only [Real.norm_eq_abs, abs_sub_comm] using hb
    exact hb'.trans (mul_le_mul_of_nonneg_left htime hS)
  have hyspace : y.2 ∈ closedBall x.2 R := by
    rw [mem_closedBall, dist_eq_norm, norm_sub_rev]
    exact (le_max_right _ _).trans hy.1.le
  have hsbound := spatial_quadratic_taylor (fun w => h (x.1, w)) x.2 y.2 hR hS hyspace hg hD hDD
  have heq : h y - h x - fderiv ℝ (fun w => h (x.1, w)) x.2 (y.2 - x.2) =
      (h (y.1, y.2) - h (x.1, y.2)) +
      (h (x.1, y.2) - h (x.1, x.2) - fderiv ℝ (fun w => h (x.1, w)) x.2 (y.2 - x.2)) := by
    rw [Prod.mk.eta, Prod.mk.eta]
    ring
  rw [heq]
  exact (abs_add_le _ _).trans (by linarith)

end GlobalPhi43.Local
