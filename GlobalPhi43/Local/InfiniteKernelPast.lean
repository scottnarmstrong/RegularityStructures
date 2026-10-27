/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.InfiniteKernelMoments
public import GlobalPhi43.Local.SmoothingComparison

/-! The constructed kernel is strictly past almost everywhere, and its
closed support preserves the exact enlarged sampled-pair geometry. -/
public noncomputable section

namespace GlobalPhi43.Local

open MeasureTheory RegularityStructures MW20 Filter Topology Set
open scoped BoundedContinuousFunction

theorem finite_kernel_zero_of_time_nonneg (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (n : ℕ) {z : ParabolicSpace} (hz : 0 ≤ z.1) :
    finiteKernelDensity Φ hΦ T hT n z = 0 := by
  have := kernelProfileMeasure_probability Φ hΦ
  induction n generalizing z with
  | zero =>
    by_contra hn
    have hφ : Φ (parabolicDilate (T / 2)⁻¹ z) ≠ 0 := by
      intro he
      apply hn
      simp only [finiteKernelDensity, convolutionIter, scaledKernelSeed_apply, he, mul_zero]
    have hs := hΦ.support (subset_tsupport Φ hφ)
    have ht : 0 ≤ (parabolicDilate (T / 2)⁻¹ z).1 := by
      exact mul_nonneg (sq_nonneg _) hz
    linarith [hs.2.1]
  | succ n ih =>
    change (∫ y, finiteKernelDensity Φ hΦ T hT n (z - y)
      ∂dyadicKernelFactor (kernelProfileMeasure Φ) (T / 2) n) = 0
    apply integral_eq_zero_of_ae
    filter_upwards [dyadicKernelFactor_ae_parabolic Φ hΦ (half_pos hT).le n] with y hy
    exact ih (by change 0 ≤ z.1 - y.1; linarith [hy.1])

/-- The strict-past property holds also at time zero for the limiting density. -/
theorem infiniteKernel_eq_zero_of_time_nonneg (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (hT₁ : T ≤ 1) {z : ParabolicSpace} (hz : 0 ≤ z.1) :
    infiniteKernel Φ hΦ T hT z = 0 := by
  have ht := (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
    (finiteKernelDensity_tendsto Φ hΦ hT hT₁)).tendsto_at z
  apply tendsto_nhds_unique ht
  simpa only [finite_kernel_zero_of_time_nonneg Φ hΦ hT _ hz] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

theorem infiniteKernelMeasure_ae_strictPast (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (hT₁ : T ≤ 1) :
    ∀ᵐ z ∂infiniteKernelMeasure Φ hΦ T hT, z.1 < 0 ∧ pdist 0 z ≤ T := by
  unfold infiniteKernelMeasure
  apply (ae_withDensity_iff
    (infiniteKernel Φ hΦ T hT).continuous.measurable.ennreal_ofReal).2
  apply ae_of_all
  intro z hz
  have hn : infiniteKernel Φ hΦ T hT z ≠ 0 := by intro he; simp [he] at hz
  refine ⟨?_, (infiniteKernel_closedPast_support Φ hΦ hT hT₁ hn).2⟩
  by_contra h
  exact hn (infiniteKernel_eq_zero_of_time_nonneg Φ hΦ hT hT₁ (le_of_not_gt h))

/-- The support closure retains closed-past geometry. -/
theorem infiniteKernel_tsupport_closedPast (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (hT₁ : T ≤ 1) {w : ParabolicSpace}
    (hw : w ∈ tsupport (infiniteKernel Φ hΦ T hT)) : w.1 ≤ 0 ∧ pdist 0 w ≤ T := by
  have hc : IsClosed {z : ParabolicSpace | z.1 ≤ 0 ∧ pdist 0 z ≤ T} :=
    (isClosed_le continuous_fst continuous_const).inter
      (isClosed_le (show Continuous (fun z : ParabolicSpace => pdist 0 z) by unfold pdist; fun_prop) continuous_const)
  apply closure_minimal (fun z hz => infiniteKernel_closedPast_support Φ hΦ hT hT₁ hz) hc hw

/-- Actual sampled endpoints lie in B^-(x,R+T), also for closed kernel support. -/
theorem add_mem_pastBall_add {x y w : ParabolicSpace} {R T : ℝ}
    (hy : y ∈ pastBall x R) (ht : w.1 ≤ 0) (hw : pdist 0 w ≤ T) :
    y + w ∈ pastBall x (R + T) := by
  refine ⟨?_, ?_⟩
  · exact (pdist_triangle x y (y + w)).trans_lt
      (add_lt_add_of_lt_of_le hy.1 (by simpa only [pdist_add_right] using hw))
  · change y.1 + w.1 < x.1
    linarith [hy.2]

end GlobalPhi43.Local
