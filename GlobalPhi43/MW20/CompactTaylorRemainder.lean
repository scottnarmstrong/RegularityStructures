module

public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Normed.Module.Convex

/-!
# Uniform quadratic Taylor remainder on a compact ball

The ambient constants are used only to prove finiteness of actual source
seminorms; no derivative-dependent constant enters a source estimate.
-/

public section

namespace GlobalPhi43.MW20

open Set
open scoped ContDiff

/-- A smooth function has a uniform first-order Taylor remainder on a compact
ball, obtained from Mathlib's derivative Lipschitz and mean-value theorems. -/
theorem compact_ball_taylor_remainder {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E]
    (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (R : ℝ) :
    ∃ K : NNReal, ∀ x ∈ Metric.closedBall (0 : E) R,
      ∀ y ∈ Metric.closedBall (0 : E) R,
        ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ (K : ℝ) * ‖y - x‖ ^ 2 := by
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  obtain ⟨K, hK⟩ := hdf.contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_closedBall (0 : E) R) (isCompact_closedBall (0 : E) R)
  refine ⟨K, ?_⟩
  intro x hx y hy
  have hseg : segment ℝ x y ⊆ Metric.closedBall (0 : E) R :=
    (convex_closedBall (0 : E) R).segment_subset hx hy
  have hb : ∀ z ∈ segment ℝ x y,
      ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ (K : ℝ) * ‖y - x‖ := by
    intro z hz
    have hl : ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ (K : ℝ) * ‖z - x‖ := by
      simpa only [dist_eq_norm] using hK.dist_le_mul z (hseg hz) x hx
    exact hl.trans (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) K.coe_nonneg)
  have hh := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le'
    (fun z _ => (hf.differentiable (by simp)).differentiableAt) hb
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  convert hh using 1; ring

end GlobalPhi43.MW20
