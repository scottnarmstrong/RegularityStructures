/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Uniform first-order Taylor estimates on compact sets

If `f(s, ·)` is differentiable with derivative `f'(s, ·)` and `f'` is jointly continuous, then the
first-order Taylor remainder of `f(s, ·)` is `o(‖h‖)` uniformly for `(s, v)` in a compact set.
-/

public section

open Set Filter Topology Metric

namespace RegularityStructures.PDE

variable {P V F : Type*} [MetricSpace P] [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Uniform Taylor estimate.** If `f(s, ·)` has derivative `f'(s, v)` at every `v` and `f'` is
continuous, then for every `ε > 0` there is `δ > 0` with
`‖f(s, v + h) - f(s, v) - f'(s, v) h‖ ≤ ε ‖h‖` for all `(s, v) ∈ K` and `‖h‖ < δ`. -/
theorem exists_uniform_taylor {f : P × V → F} {f' : P × V → V →L[ℝ] F} (hf' : Continuous f')
    (hf : ∀ s v, HasFDerivAt (fun w => f (s, w)) (f' (s, v)) v)
    {K : Set (P × V)} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ p ∈ K, ∀ h : V, ‖h‖ < δ → ‖f (p.1, p.2 + h) - f p - f' p h‖ ≤ ε * ‖h‖ := by
  set K' : Set (P × V) := (fun q : (P × V) × V => (q.1.1, q.1.2 + q.2)) '' (K ×ˢ closedBall 0 1)
  have hK' : IsCompact K' :=
    (hK.prod (isCompact_closedBall 0 1)).image (by fun_prop)
  obtain ⟨δ, hδ, hU⟩ := Metric.uniformContinuousOn_iff.1
    (hK'.uniformContinuousOn_of_continuous hf'.continuousOn) ε hε
  refine ⟨min δ 1, lt_min hδ one_pos, fun p hp h hh => ?_⟩
  have hmemK' : ∀ q ∈ ball p.2 (min δ 1), (p.1, q) ∈ K' := by
    intro q hq
    refine ⟨(p, q - p.2), ⟨hp, ?_⟩, by simp⟩
    rw [mem_closedBall, dist_zero_right, ← dist_eq_norm]
    exact (mem_ball.1 hq).le.trans (min_le_right _ _)
  have hpK' : p ∈ K' := by
    simpa using hmemK' p.2 (mem_ball_self (lt_min hδ one_pos))
  have hbound : ∀ q ∈ ball p.2 (min δ 1), ‖f' (p.1, q) - f' p‖ ≤ ε := by
    intro q hq
    have hd : dist (p.1, q) p < δ := by
      rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
      exact (mem_ball.1 hq).trans_le (min_le_left _ _)
    rw [← dist_eq_norm]
    exact (hU _ (hmemK' q hq) _ hpK' hd).le
  have hderiv : ∀ q ∈ ball p.2 (min δ 1),
      HasFDerivWithinAt (fun w => f (p.1, w)) (f' (p.1, q)) (ball p.2 (min δ 1)) q :=
    fun q _ => (hf p.1 q).hasFDerivWithinAt
  have hmem : p.2 + h ∈ ball p.2 (min δ 1) := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact hh
  have := (convex_ball p.2 (min δ 1)).norm_image_sub_le_of_norm_hasFDerivWithin_le' hderiv
    hbound (mem_ball_self (lt_min hδ one_pos)) hmem
  simpa using this

end RegularityStructures.PDE

end
