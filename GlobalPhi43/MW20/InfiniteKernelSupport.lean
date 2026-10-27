module

public import GlobalPhi43.MW20.InfiniteKernel
public import GlobalPhi43.MW20.ConvolutionSupport

/-!
# A common compact support for the constructed kernel densities
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Filter Topology
open scoped BoundedContinuousFunction

/-- The actual scaled seed vanishes outside its ordinary-norm radius at
source scales. This coarse compact-support bound is not a printed parabolic
support-radius claim. -/
theorem scaledKernelSeed_eq_zero_of_norm_gt (Φ : ParabolicSpace → ℝ)
    (hΦ : KernelProfile Φ) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    {x : ParabolicSpace} (hx : c < ‖x‖) : scaledKernelSeed Φ hΦ c hc x = 0 := by
  by_contra hn
  have hp : Φ (parabolicDilate c⁻¹ x) ≠ 0 := by
    intro hp
    apply hn
    simp only [scaledKernelSeed_apply, hp, mul_zero]
  have hb := norm_le_one_of_mem_kernelPastUnitBall
    (hΦ.support (subset_tsupport _ hp))
  have hs := (norm_parabolicDilate_le_scale hc.le hc1 (parabolicDilate c⁻¹ x)).trans
    (mul_le_mul_of_nonneg_left hb hc.le)
  rw [parabolicDilate_parabolicDilate_inv hc.ne'] at hs
  exact (not_le_of_gt hx) (by simpa only [mul_one] using hs)

/-- All finite densities have a common bounded support, with the summable
tail radius accounted for explicitly. -/
theorem finiteKernelDensity_eq_zero_of_norm_gt (Φ : ParabolicSpace → ℝ)
    (hΦ : KernelProfile Φ) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (n : ℕ) {x : ParabolicSpace} (hx : T < ‖x‖) :
    finiteKernelDensity Φ hΦ T hT n x = 0 := by
  have := kernelProfileMeasure_probability Φ hΦ
  let R : ℕ → ℝ := fun j => T * (1 - (1 / 2 : ℝ) ^ (j + 1))
  let r : ℕ → ℝ := fun j => (T / 2 * 1 / 2) * (1 / 2 : ℝ) ^ j
  have hseed : ∀ y, R 0 < ‖y‖ → scaledKernelSeed Φ hΦ (T / 2) (half_pos hT) y = 0 := by
    intro y hy
    apply scaledKernelSeed_eq_zero_of_norm_gt Φ hΦ (half_pos hT) (by linarith)
    dsimp [R] at hy
    norm_num at hy
    linarith
  have hR : ∀ j, R (j + 1) = R j + r j := by
    intro j
    dsimp [R, r]
    rw [pow_succ, pow_succ]
    ring
  have hμ := dyadicKernelFactor_ae_norm_le (kernelProfileMeasure Φ)
    (by positivity : 0 ≤ T / 2) (by linarith : T / 2 ≤ 1)
    (kernelProfileMeasure_ae_norm_le Φ hΦ)
  apply convolutionIter_eq_zero_of_norm_gt _ _ R r hseed hR hμ n x
  have hp : 0 ≤ (1 / 2 : ℝ) ^ (n + 1) := by positivity
  dsimp [R]
  nlinarith

/-- Every finite density is compactly supported in the same closed ball. -/
theorem finiteKernelDensity_hasCompactSupport (Φ : ParabolicSpace → ℝ)
    (hΦ : KernelProfile Φ) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) (n : ℕ) :
    HasCompactSupport (finiteKernelDensity Φ hΦ T hT n) := by
  apply (isCompact_closedBall (0 : ParabolicSpace) T).of_isClosed_subset isClosed_closure
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  simp only [Metric.mem_closedBall, dist_zero_right]
  by_contra hn
  exact hx (finiteKernelDensity_eq_zero_of_norm_gt Φ hΦ hT hT1 n (lt_of_not_ge hn))

/-- The uniform limit retains the same bounded support. -/
theorem infiniteKernel_eq_zero_of_norm_gt (Φ : ParabolicSpace → ℝ)
    (hΦ : KernelProfile Φ) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    {x : ParabolicSpace} (hx : T < ‖x‖) : infiniteKernel Φ hΦ T hT x = 0 := by
  have ht := (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
    (finiteKernelDensity_tendsto Φ hΦ hT hT1)).tendsto_at x
  apply tendsto_nhds_unique ht
  simpa only [finiteKernelDensity_eq_zero_of_norm_gt Φ hΦ hT hT1 _ hx] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

/-- The constructed smooth density is compactly supported. -/
theorem infiniteKernel_hasCompactSupport (Φ : ParabolicSpace → ℝ)
    (hΦ : KernelProfile Φ) {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) :
    HasCompactSupport (infiniteKernel Φ hΦ T hT) := by
  apply (isCompact_closedBall (0 : ParabolicSpace) T).of_isClosed_subset isClosed_closure
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  simp only [Metric.mem_closedBall, dist_zero_right]
  by_contra hn
  exact hx (infiniteKernel_eq_zero_of_norm_gt Φ hΦ hT hT1 (lt_of_not_ge hn))

end GlobalPhi43.MW20
