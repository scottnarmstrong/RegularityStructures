/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.HeatOperatorSlices
public import Mathlib.Analysis.Normed.Operator.Basic

/-! The spatial Hessian restriction does not increase its operator norm. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures
open scoped ContDiff

 theorem spatial_slice_hessian_norm_le {h : ParabolicSpace → ℝ} (hh : ContDiff ℝ ∞ h)
    (p : ParabolicSpace) {C : ℝ} (hC : 0 ≤ C) (hbound : ‖fderiv ℝ (fderiv ℝ h) p‖ ≤ C) :
    ‖fderiv ℝ (fderiv ℝ (fun w : Fin 3 → ℝ => h (p.1, w))) p.2‖ ≤ C := by
  let H := fderiv ℝ (fderiv ℝ (fun w : Fin 3 → ℝ => h (p.1, w))) p.2
  apply H.opNorm_le_bound hC
  intro v₁
  apply (H v₁).opNorm_le_bound (mul_nonneg hC (norm_nonneg v₁))
  intro v₂
  change ‖fderiv ℝ (fderiv ℝ (fun w : Fin 3 → ℝ => h (p.1, w))) p.2 v₁ v₂‖ ≤ _
  rw [spatial_slice_second_joint hh]
  have hb := ((fderiv ℝ (fderiv ℝ h) p (0, v₁)).le_opNorm (0, v₂)).trans
    (mul_le_mul_of_nonneg_right
      (((fderiv ℝ (fderiv ℝ h) p).le_opNorm (0, v₁)).trans
        (mul_le_mul_of_nonneg_right hbound (norm_nonneg _))) (norm_nonneg _))
  simpa only [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg v₁),
    max_eq_right (norm_nonneg v₂)] using hb

end GlobalPhi43.Local
