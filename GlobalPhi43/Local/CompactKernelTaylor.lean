/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.SpatialHessianNorm
public import GlobalPhi43.Local.ParabolicTaylor
public import Mathlib.Analysis.Normed.Group.Bounded

/-! A compact smooth kernel has one global parabolic Taylor constant.
This constant is chosen before every target, source and radius. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20
open scoped ContDiff

 theorem exists_compact_kernel_taylor_bound {k : ParabolicSpace → ℝ}
    (hk : ContDiff ℝ ∞ k) (hck : HasCompactSupport k) :
    ∃ S ≥ 0, ∀ (x y : ParabolicSpace) (R : ℝ), 0 ≤ R → y ∈ pastBall x R →
      |k y - k x - fderiv ℝ (fun w : Fin 3 → ℝ => k (x.1, w)) x.2 (y.2 - x.2)| ≤
        2 * S * R ^ 2 := by
  have hdk : ContDiff ℝ ∞ (fderiv ℝ k) := hk.fderiv_right (by simp)
  obtain ⟨C₁, hC₁⟩ := hdk.continuous.bounded_above_of_compact_support (hck.fderiv ℝ)
  obtain ⟨C₂, hC₂⟩ := (hdk.continuous_fderiv (by simp)).bounded_above_of_compact_support
    ((hck.fderiv ℝ).fderiv ℝ)
  have hC₁0 : 0 ≤ C₁ := (norm_nonneg (fderiv ℝ k 0)).trans (hC₁ 0)
  have hC₂0 : 0 ≤ C₂ := (norm_nonneg (fderiv ℝ (fderiv ℝ k) 0)).trans (hC₂ 0)
  refine ⟨max C₁ C₂, hC₁0.trans (le_max_left _ _), ?_⟩
  intro x y R hR hy
  apply parabolic_quadratic_taylor k x y hR (hC₁0.trans (le_max_left _ _)) hy
  · intro t _
    exact (hk.differentiable (by simp) (t, y.2)).comp t
      ((differentiableAt_id).prodMk (differentiableAt_const y.2))
  · intro t _
    rw [source_time_deriv_eq_fderiv k (t, y.2) (hk.differentiable (by simp) _)]
    have hb := ((fderiv ℝ k (t, y.2)).le_opNorm ((1, 0) : ParabolicSpace)).trans
      (mul_le_mul_of_nonneg_right (hC₁ (t, y.2)) (norm_nonneg _))
    have hh : |fderiv ℝ k (t, y.2) (1, 0)| ≤ C₁ := by
      simpa only [Real.norm_eq_abs, Prod.norm_def, norm_one, norm_zero, max_eq_left (by norm_num : (0 : ℝ) ≤ 1), mul_one] using hb
    exact hh.trans (le_max_left _ _)
  · intro z _
    exact (smooth_spatial_slice hk x.1).differentiable (by simp) z
  · intro z _
    have hs : ContDiff ℝ ∞ (fderiv ℝ (fun w : Fin 3 → ℝ => k (x.1, w))) :=
      (smooth_spatial_slice hk x.1).fderiv_right (by simp)
    exact hs.differentiable (by simp) z
  · intro z _
    exact (spatial_slice_hessian_norm_le hk (x.1, z) hC₂0 (hC₂ (x.1, z))).trans (le_max_right _ _)

end GlobalPhi43.Local
