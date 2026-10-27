/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.GaussianFundamentalIdentity
public import GlobalPhi43.Local.GaussianChangeVariables

/-! Fundamental identity for the actual ordinary Euclidean heat kernel.
The finite time endpoint is past the support of the compact smooth test. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MeasureTheory Set
open scoped ContDiff

/-- Fixed-endpoint ordinary heat-kernel identity for compact smooth tests. -/
theorem heatKernel_fundamental_identity_at_time {φ : ParabolicSpace → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hcomp : HasCompactSupport φ) (y : Fin 3 → ℝ)
    {T : ℝ} (hT : 0 < T) (hzero : ∀ w : Fin 3 → ℝ, φ (T, w) = 0) :
    (∫ t in (0 : ℝ)..T, ∫ w : Fin 3 → ℝ,
      heatKernelR4 (t, w) * (-heatTestGenerator φ (t, y - w))) = φ (0, y) := by
  rw [← gaussian_fundamental_identity_at_time hφ hcomp y hT hzero]
  apply intervalIntegral.integral_congr_ae
  apply ae_of_all
  intro t ht
  rw [uIoc_of_le hT.le] at ht
  exact (gaussian_change_variables ht.1 (fun w : Fin 3 → ℝ =>
    -heatTestGenerator φ (t, y - w))).symm

end GlobalPhi43.Local
