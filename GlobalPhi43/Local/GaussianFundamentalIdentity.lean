/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.GaussianJointContinuity
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Fundamental-solution identity in Gaussian change-of-variables form.
The actual heat kernel is used; all endpoint and integrability obligations
follow from the compact smooth test, not from a representation hypothesis. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MeasureTheory Real Set
open scoped ContDiff

/-- The initial test value is recovered at any positive endpoint where the
entire spatial test slice vanishes. This permits a preselected cutoff time. -/
theorem gaussian_fundamental_identity_at_time {φ : ParabolicSpace → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hcomp : HasCompactSupport φ) (y : Fin 3 → ℝ)
    {T : ℝ} (hT : 0 < T) (hzero : ∀ w : Fin 3 → ℝ, φ (T, w) = 0) :
    (∫ t in (0 : ℝ)..T, ∫ z : Fin 3 → ℝ,
      gaussKernel 1 z * (-heatTestGenerator φ (t, y - √t • z))) = φ (0, y) := by
  have hF := continuous_gaussian_joint_average hφ.continuous hcomp y
  have hG := continuous_gaussian_joint_average (heatTestGenerator_contDiff hφ).continuous
    (heatTestGenerator_hasCompactSupport hcomp) y
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT.le hF.continuousOn
    (fun t ht => hasDerivAt_gaussian_heat_generator hφ hcomp ht.1 y) (hG.intervalIntegrable 0 T)
  have hend : (∫ z : Fin 3 → ℝ, gaussKernel 1 z * φ (T, y - √T • z)) = 0 := by
    apply integral_eq_zero_of_ae
    apply ae_of_all
    intro z
    simp [hzero]
  rw [hend, gaussian_joint_average_at_zero, zero_sub] at hFTC
  simp_rw [mul_neg, integral_neg]
  rw [intervalIntegral.integral_neg, hFTC, neg_neg]

end GlobalPhi43.Local
