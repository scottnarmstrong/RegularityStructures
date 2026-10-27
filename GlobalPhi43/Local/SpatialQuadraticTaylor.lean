/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.RadiusGeometry
public import Mathlib.Analysis.Calculus.MeanValue

/-! The spatial Taylor step in the ordinary-heat affine estimate. The
second derivative bound is explicit; no caloric derivative estimate is
asserted by this calculus component. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures Set Metric

/-- On a convex spatial ball, a bounded second derivative yields the exact
quadratic affine approximation, via two mean-value inequalities. -/
theorem spatial_quadratic_taylor (g : (Fin 3 → ℝ) → ℝ) (a b : Fin 3 → ℝ)
    {R S : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S) (hb : b ∈ closedBall a R)
    (hg : ∀ z ∈ closedBall a R, DifferentiableAt ℝ g z)
    (hD : ∀ z ∈ closedBall a R, DifferentiableAt ℝ (fderiv ℝ g) z)
    (hDD : ∀ z ∈ closedBall a R, ‖fderiv ℝ (fderiv ℝ g) z‖ ≤ S) :
    |g b - g a - fderiv ℝ g a (b - a)| ≤ S * R ^ 2 := by
  have ha : a ∈ closedBall a R := mem_closedBall_self hR
  have hconv : Convex ℝ (closedBall a R) := convex_closedBall a R
  have hderiv : ∀ z ∈ closedBall a R, ‖fderiv ℝ g z - fderiv ℝ g a‖ ≤ S * R := by
    intro z hz
    have hm := hconv.norm_image_sub_le_of_norm_fderiv_le hD hDD ha hz
    have hzR : ‖z - a‖ ≤ R := by simpa only [mem_closedBall, dist_eq_norm] using hz
    exact hm.trans (mul_le_mul_of_nonneg_left hzR hS)
  have hm := hconv.norm_image_sub_le_of_norm_fderiv_le' hg hderiv ha hb
  have hbR : ‖b - a‖ ≤ R := by simpa only [mem_closedBall, dist_eq_norm] using hb
  rw [Real.norm_eq_abs] at hm
  exact hm.trans (by nlinarith [mul_le_mul_of_nonneg_left hbR (mul_nonneg hS hR)])

end GlobalPhi43.Local
