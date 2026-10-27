/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.PastBoxAffineGerms
public import GlobalPhi43.MW20.ReconstructionBallClosure

/-! Identification of the unit analytic carrier with the literal closure
of the source past ball, for the exact scaling interface. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Set Metric

 theorem unitHeatPastCarrier_eq_closure : unitHeatPastCarrier = closure (pastBall 0 1) := by
  apply subset_antisymm
  · intro q hq
    apply reconstruction_mem_closure_pastBall 0 q (by norm_num) _ hq.2
    have hn : ‖q‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hq.1
    have ht : |q.1| ≤ 1 := by
      have hh : ‖q.1‖ ≤ ‖q‖ := norm_fst_le q
      simpa only [Real.norm_eq_abs] using hh.trans hn
    have hs : ‖q.2‖ ≤ 1 := (norm_snd_le q).trans hn
    unfold pdist
    simp only [Prod.fst_zero, Prod.snd_zero, zero_sub, abs_neg, norm_neg]
    apply max_le _ hs
    exact (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 1)).mpr (by simpa using ht)
  · exact closure_minimal unit_pastBall_subset_carrier unitHeatPastCarrier_isCompact.isClosed

end GlobalPhi43.Local
