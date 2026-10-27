/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.UnitHeatSource

/-! Fixed lower slice and core target geometry for the causal cutoff formula. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures Set Metric

 theorem fixed_cutoff_lower_slice_zero {χ : ParabolicSpace → ℝ}
    (hs : tsupport χ ⊆ closedBall (0 : ParabolicSpace) (3 / 4 : ℝ)) (z : Fin 3 → ℝ) :
    χ (-1, z) = 0 := by
  by_contra hz
  have hnorm : ‖((-1, z) : ParabolicSpace)‖ ≤ 3 / 4 := by
    simpa only [mem_closedBall, dist_zero_right] using hs (subset_tsupport χ hz)
  have hlo : ‖(-1 : ℝ)‖ ≤ ‖((-1, z) : ParabolicSpace)‖ := by
    rw [Prod.norm_def]
    exact le_max_left _ _
  rw [norm_neg, norm_one] at hlo
  linarith

 theorem unit_core_time_lower {p : ParabolicSpace} (hp : ‖p‖ ≤ 1 / 4) : -1 < p.1 := by
  have hfst : ‖p.1‖ ≤ ‖p‖ := by rw [Prod.norm_def]; exact le_max_left _ _
  have ht : |p.1| ≤ 1 / 4 := by simpa only [Real.norm_eq_abs] using hfst.trans hp
  linarith [(abs_le.mp ht).1]

 theorem fixed_cutoff_core_one {χ : ParabolicSpace → ℝ}
    (hone : ∀ q ∈ closedBall (0 : ParabolicSpace) (1 / 2 : ℝ), χ q = 1)
    {p : ParabolicSpace} (hp : ‖p‖ ≤ 1 / 4) : χ p = 1 := by
  apply hone p
  rw [mem_closedBall, dist_zero_right]
  linarith

 theorem unit_source_time_lower {q : ParabolicSpace} (hq : q ∈ unitHeatSourceDomain) : -1 < q.1 := by
  have hn : ‖q‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hq.1
  have hfst : ‖q.1‖ ≤ ‖q‖ := by rw [Prod.norm_def]; exact le_max_left _ _
  have ht : |q.1| < 1 := by simpa only [Real.norm_eq_abs] using hfst.trans_lt hn
  exact (abs_lt.mp ht).1

end GlobalPhi43.Local
