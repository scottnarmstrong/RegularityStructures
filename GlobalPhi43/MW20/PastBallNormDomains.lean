module

public import GlobalPhi43.MW20.DyadicKernelSupport
public import GlobalPhi43.Local.SmoothingComparison

/-! Compact ambient envelopes for the actual source past balls.
These envelopes are used only to prove source norm finiteness. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Local Set

/-- Every source past ball is contained in an explicit compact ambient ball. -/
theorem pastBall_subset_compact_ball (x : ParabolicSpace) {T : ℝ} (hT : 0 ≤ T) :
    pastBall x T ⊆ Metric.closedBall 0 (‖x‖ + max (T ^ 2) T) := by
  intro y hy
  have he : x + (y - x) = y := by abel
  have hd : pdist 0 (y - x) ≤ T := by
    rw [← pdist_add_right x (y - x), he]
    exact hy.1.le
  have hn := norm_le_of_pdist_zero_le hT hd
  rw [Metric.mem_closedBall, dist_zero_right]
  calc
    ‖y‖ = ‖x + (y - x)‖ := by rw [he]
    _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
    _ ≤ ‖x‖ + max (T ^ 2) T := add_le_add le_rfl hn

end GlobalPhi43.MW20
