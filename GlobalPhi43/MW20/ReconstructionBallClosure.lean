module

public import GlobalPhi43.Local.RadiusGeometry
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Topology.Order.DenselyOrdered

/-! The exact closure of the MW20 past ball. The reconstruction proof tests
coherence at terminal-time and radius-boundary points, so the open source
hypothesis must first be extended there by continuity. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Local Set Metric

/-- The exact past ball is a time interval times a spatial sup-norm ball. -/
theorem reconstruction_pastBall_eq_prod (x : ParabolicSpace) {r : ℝ} (hr : 0 < r) :
    pastBall x r = Ioo (x.1 - r ^ 2) x.1 ×ˢ ball x.2 r := by
  ext y
  constructor
  · intro hy
    have htime : |x.1 - y.1| < r ^ 2 :=
      (Real.sqrt_lt (abs_nonneg _) hr.le).mp ((le_max_left _ _).trans_lt hy.1)
    have hs : ‖x.2 - y.2‖ < r := (le_max_right _ _).trans_lt hy.1
    refine ⟨⟨?_, hy.2⟩, ?_⟩
    · linarith [le_abs_self (x.1 - y.1)]
    · simpa only [mem_ball, dist_eq_norm, norm_sub_rev] using hs
  · intro hy
    refine ⟨?_, hy.1.2⟩
    apply max_lt
    · apply (Real.sqrt_lt (abs_nonneg _) hr.le).mpr
      rw [abs_of_pos (sub_pos.mpr hy.1.2)]
      linarith [hy.1.1]
    · simpa only [mem_ball, dist_eq_norm, norm_sub_rev] using hy.2

/-- Closed-past support points are in the closure of the source testing ball,
with exactly the same radius. No metric-equivalence constant is introduced. -/
theorem reconstruction_mem_closure_pastBall (x y : ParabolicSpace) {r : ℝ}
    (hr : 0 < r) (hd : pdist x y ≤ r) (ht : y.1 ≤ x.1) :
    y ∈ closure (pastBall x r) := by
  rw [reconstruction_pastBall_eq_prod x hr, closure_prod_eq,
    closure_Ioo (show x.1 - r ^ 2 ≠ x.1 by nlinarith [sq_pos_of_pos hr]), closure_ball x.2 hr.ne']
  have hsqrt : Real.sqrt |x.1 - y.1| ≤ r := (le_max_left _ _).trans hd
  have habs : |x.1 - y.1| ≤ r ^ 2 := by
    nlinarith [Real.sq_sqrt (abs_nonneg (x.1 - y.1)), Real.sqrt_nonneg |x.1 - y.1|]
  refine ⟨⟨?_, ht⟩, ?_⟩
  · linarith [le_abs_self (x.1 - y.1)]
  · have hs : ‖x.2 - y.2‖ ≤ r := (le_max_right _ _).trans hd
    simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev] using hs

end GlobalPhi43.MW20
