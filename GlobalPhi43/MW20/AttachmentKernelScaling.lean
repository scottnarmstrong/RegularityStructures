module

public import GlobalPhi43.MW20.InfiniteKernel

/-! Dilation covariance for the constructed MW20 density, using convergence of
the finite convolution kernels. -/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Filter Topology
open scoped BoundedContinuousFunction

/-- Every actual finite density has the source's homogeneous dimension five. -/
theorem finiteKernelDensity_dilate (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (n : ℕ) (x : ParabolicSpace) :
    finiteKernelDensity Φ hΦ T hT n (parabolicDilate T x) =
      (T^5)⁻¹ * finiteKernelDensity Φ hΦ 1 (by norm_num) n x := by
  have := kernelProfileMeasure_probability Φ hΦ
  induction n generalizing x with
  | zero =>
    simp only [finiteKernelDensity, convolutionIter, scaledKernelSeed_apply,
      ← parabolicDilate_mul]
    have hc : (T/2)⁻¹*T = (1/2 : ℝ)⁻¹ := by field_simp
    rw [hc]
    have ha : ((T/2)^5)⁻¹ = (T^5)⁻¹ * (((1/2 : ℝ)^5)⁻¹) := by
      field_simp
    rw [ha]
    ring
  | succ n ih =>
    change (∫ y, finiteKernelDensity Φ hΦ T hT n (parabolicDilate T x-y)
      ∂(kernelProfileMeasure Φ).map (parabolicDilate (T/2/2^(n+1)))) =
      (T^5)⁻¹ * ∫ y, finiteKernelDensity Φ hΦ 1 (by norm_num) n (x-y)
        ∂(kernelProfileMeasure Φ).map (parabolicDilate (1/2/2^(n+1)))
    rw [integral_map (measurable_parabolicDilate _).aemeasurable
      (show AEStronglyMeasurable (fun y => finiteKernelDensity Φ hΦ T hT n
          (parabolicDilate T x-y)) _ from
        ((finiteKernelDensity Φ hΦ T hT n).continuous.comp
          (continuous_const.sub continuous_id)).aestronglyMeasurable),
      integral_map (measurable_parabolicDilate _).aemeasurable
      (show AEStronglyMeasurable (fun y => finiteKernelDensity Φ hΦ 1 (by norm_num) n
          (x-y)) _ from
        ((finiteKernelDensity Φ hΦ 1 (by norm_num) n).continuous.comp
          (continuous_const.sub continuous_id)).aestronglyMeasurable),
      ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    have hc : T*(1/2/2^(n+1)) = T/2/2^(n+1) := by ring
    have he : parabolicDilate T x-parabolicDilate (T/2/2^(n+1)) y =
        parabolicDilate T (x-parabolicDilate (1/2/2^(n+1)) y) := by
      rw [parabolicDilate_sub, ← parabolicDilate_mul, hc]
    rw [he, ih]

/-- The source dilation identity passes to the actual uniform limit. -/
theorem infiniteKernel_dilate (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (hT₁ : T ≤ 1) (x : ParabolicSpace) :
    infiniteKernel Φ hΦ T hT (parabolicDilate T x) =
      (T^5)⁻¹ * infiniteKernel Φ hΦ 1 (by norm_num) x := by
  have ht := (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
    (finiteKernelDensity_tendsto Φ hΦ hT hT₁)).tendsto_at (parabolicDilate T x)
  have h1 := (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
    (finiteKernelDensity_tendsto Φ hΦ (by norm_num : (0 : ℝ)<1) le_rfl)).tendsto_at x
  apply tendsto_nhds_unique ht
  simpa only [finiteKernelDensity_dilate Φ hΦ hT] using h1.const_mul (T^5)⁻¹

/-- Actual Ψ_T is the rescaled actual Ψ_1, with the exact source Jacobian. -/
theorem infiniteKernel_eq_rescaled_unit (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (hT₁ : T ≤ 1) (y : ParabolicSpace) :
    infiniteKernel Φ hΦ T hT y =
      (T^5)⁻¹ * infiniteKernel Φ hΦ 1 (by norm_num) (parabolicDilate T⁻¹ y) := by
  simpa only [parabolicDilate_parabolicDilate_inv hT.ne'] using
    infiniteKernel_dilate Φ hΦ hT hT₁ (parabolicDilate T⁻¹ y)

end GlobalPhi43.MW20
