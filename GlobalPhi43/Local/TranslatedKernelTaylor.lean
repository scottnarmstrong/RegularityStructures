/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.CompactKernelTaylor

/-! Translation preserves the exact past-ball Taylor geometry. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures
open scoped ContDiff

 theorem pastBall_sub_right {x y q : ParabolicSpace} {R : ℝ} (hy : y ∈ pastBall x R) :
    y - q ∈ pastBall (x - q) R := by
  constructor
  · simpa only [pdist, Prod.fst_sub, Prod.snd_sub, sub_sub_sub_cancel_right] using hy.1
  · change y.1 - q.1 < x.1 - q.1
    linarith [hy.2]

 theorem translated_kernel_taylor {k : ParabolicSpace → ℝ} (hk : ContDiff ℝ ∞ k) {S : ℝ}
    (hTaylor : ∀ (x y : ParabolicSpace) (R : ℝ), 0 ≤ R → y ∈ pastBall x R →
      |k y - k x - fderiv ℝ (fun w : Fin 3 → ℝ => k (x.1, w)) x.2 (y.2 - x.2)| ≤ 2 * S * R ^ 2)
    (x y q : ParabolicSpace) {R : ℝ} (hR : 0 ≤ R) (hy : y ∈ pastBall x R) :
    |k (y - q) - k (x - q) - fderiv ℝ k (x - q) (0, y.2 - x.2)| ≤ 2 * S * R ^ 2 := by
  have hh := hTaylor (x - q) (y - q) R hR (pastBall_sub_right hy)
  have hdiff : (y - q).2 - (x - q).2 = y.2 - x.2 := by
    change (y.2 - q.2) - (x.2 - q.2) = y.2 - x.2
    abel
  rw [spatial_slice_fderiv (hk.differentiable (by simp))] at hh
  simpa only [ContinuousLinearMap.comp_apply, heatSpatialInsert, ContinuousLinearMap.prod_apply,
    zero_apply, ContinuousLinearMap.id_apply, hdiff, Prod.mk.eta] using hh

end GlobalPhi43.Local
