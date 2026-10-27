/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.PastAffineError
public import GlobalPhi43.Local.UnitHeatSource

/-! The literal unit past ball lies in the closed past carrier, and the
affine infimum depends only on field values on its actual testing ball. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures Set Metric

 theorem unit_pastBall_subset_carrier : pastBall (0 : ParabolicSpace) 1 ⊆ unitHeatPastCarrier := by
  intro q hq
  have hρ : max (Real.sqrt |(0 : ℝ) - q.1|) ‖(0 : Fin 3 → ℝ) - q.2‖ < 1 := hq.1
  have ht : |q.1| < 1 := by
    have hh := (Real.sqrt_lt (abs_nonneg ((0 : ℝ) - q.1)) (by norm_num : (0 : ℝ) ≤ 1)).mp
      ((le_max_left _ _).trans_lt hρ)
    simpa only [zero_sub, abs_neg, one_pow] using hh
  have hx : ‖q.2‖ < 1 := by simpa only [zero_sub, norm_neg] using (le_max_right _ _).trans_lt hρ
  have htime : q.1 < 0 := hq.2
  refine ⟨?_, htime.le⟩
  rw [mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs]
  exact max_le ht.le hx.le

 theorem pastAffineError_congr {f g : ParabolicSpace → ℝ} {x : ParabolicSpace} {R : ℝ}
    (he : ∀ y ∈ pastBall x R, f y = g y) : pastAffineError f x R = pastAffineError g x R := by
  unfold pastAffineError
  apply iInf_congr
  intro c
  apply iInf_congr
  intro ν
  apply iSup_congr
  intro y
  apply iSup_congr
  intro hy
  rw [he y hy]

end GlobalPhi43.Local
