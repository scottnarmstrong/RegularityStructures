/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.InfiniteKernelPast
public import GlobalPhi43.Local.SmoothingPowers
public import GlobalPhi43.Local.TimeFreeGeometry

/-! Smoothing comparison for the constructed MW20 kernel, local continuity,
sampled endpoints and the three-point bound for all time orders. -/
public noncomputable section

namespace GlobalPhi43.Local

open MeasureTheory RegularityStructures MW20 Set
open scoped BigOperators

/-- The native smoothing comparison. The incoming causal remainder is the
small-past quantity to be absorbed later, not an assumed Schauder theorem. -/
theorem kernel_smoothing_comparison {I : Type*} (A : Finset I) (β : I → ℝ)
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (U : ParabolicSpace → ParabolicSpace → ℝ) (ν : ParabolicSpace → Fin 3 → ℝ)
    {r d R T S γ M Q : ℝ} (hd : 0 < d) (hT : 0 < T) (hT₁ : T ≤ 1)
    (hR : 0 ≤ R) (hRd : R ≤ d / 2)
    (hTd : T < d / 4) (hTS : T < S) (hγ : 0 ≤ γ) (hM : 0 ≤ M) (hQ : 0 ≤ Q)
    (hβ : ∀ i ∈ A, 0 ≤ β i) (hβγ : ∀ i ∈ A, β i ≤ γ)
    (hU : ContinuousOn (fun p : ParabolicSpace × ParabolicSpace => U p.1 p.2)
      (sourceCylinder r ×ˢ sourceCylinder r))
    {x y : ParabolicSpace} (hx : x ∈ cylinderInterior r d) (hy : y ∈ pastBall x R)
    (hthree : ∀ b ∈ sourceCylinder r, b ∈ symmetricBall x (d / 2) →
      ∀ z ∈ sourceCylinder r, z ∈ symmetricBall b (d / 4) →
      |U x z - U x b - U b z| ≤
        M * ∑ i ∈ A, pdist x b ^ β i * pdist b z ^ (γ - β i))
    (hrem : ∀ z ∈ pastBall y S,
      |U y z - spatialLinear (ν y) (z - y)| ≤ Q * pdist y z ^ γ) :
    |(∫ w, infiniteKernel Φ hΦ T hT w * U x (y + w)) - U x y| ≤
      M * (∑ i ∈ A, R ^ β i * T ^ (γ - β i)) + Q * T ^ γ := by
  have hprob := infiniteKernelMeasure_probability Φ hΦ hT hT₁
  have hxD := cylinderInterior_mem_domain hd.le hx
  have hendpoint (w : ParabolicSpace) (hw : w ∈ tsupport (infiniteKernel Φ hΦ T hT)) :
      y + w ∈ sourceCylinder r := by
    have hs := infiniteKernel_tsupport_closedPast Φ hΦ hT hT₁ hw
    have he := add_mem_pastBall_add hy hs.1 hs.2
    exact cylinderInterior_mem_domain (by norm_num : (0 : ℝ) ≤ 0)
      (pastBall_subset_interior (by norm_num) (by positivity) (by linarith) hx he)
  have hcontinuous : ContinuousOn (fun w => U x (y + w))
      (tsupport (infiniteKernel Φ hΦ T hT)) := by
    have hm : ContinuousOn (fun w : ParabolicSpace => (x, y + w))
        (tsupport (infiniteKernel Φ hΦ T hT)) := by fun_prop
    exact hU.comp hm (fun w hw => ⟨hxD, hendpoint w hw⟩)
  have hint := integrable_infiniteKernelMeasure_of_continuousOn Φ hΦ hT hT₁ _ hcontinuous
  have hys : y ∈ sourceCylinder r := cylinderInterior_mem_domain (by norm_num : (0 : ℝ) ≤ 0)
    (pastBall_subset_interior (by norm_num) hR (by linarith) hx hy)
  have hbound := recentered_smoothing_comparison_powers A β
    (infiniteKernelMeasure Φ hΦ T hT) U x y (ν y) hγ hM hQ hβ hβγ hy.1.le
    hint (infiniteKernelMeasure_coordinate_integrable Φ hΦ hT hT₁)
    (integral_coordinate_infiniteKernelMeasure_eq_zero Φ hΦ hT hT₁)
    ((infiniteKernelMeasure_ae_closedPast Φ hΦ hT hT₁).mono fun _ h => h.2) ?_ ?_
  · simpa only [integral_infiniteKernelMeasure Φ hΦ hT hT₁] using hbound
  · filter_upwards [infiniteKernelMeasure_ae_strictPast Φ hΦ hT hT₁] with w hw
    have hzD : y + w ∈ sourceCylinder r := cylinderInterior_mem_domain (by norm_num : (0 : ℝ) ≤ 0)
      (pastBall_subset_interior (by norm_num) (by positivity) (by linarith) hx
        (add_mem_pastBall_add hy hw.1.le hw.2))
    exact hthree y hys (by change pdist x y < d / 2; exact hy.1.trans_le hRd)
      (y + w) hzD (by change pdist y (y + w) < d / 4; rw [pdist_add_right]; exact hw.2.trans_lt hTd)
  · filter_upwards [infiniteKernelMeasure_ae_strictPast Φ hΦ hT hT₁] with w hw
    have hp : y + w ∈ pastBall y S := ⟨by rw [pdist_add_right]; exact hw.2.trans_lt hTS,
      by change y.1 + w.1 < y.1; linarith [hw.1]⟩
    simpa only [add_sub_cancel_left] using hrem (y + w) hp

end GlobalPhi43.Local
