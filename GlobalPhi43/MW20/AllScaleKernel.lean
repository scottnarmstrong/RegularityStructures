module

public import GlobalPhi43.MW20.AttachmentKernelScaling
public import GlobalPhi43.Local.ParabolicTransport

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Filter Topology
open scoped BoundedContinuousFunction NNReal

/-- Global ordinary-norm dilation bound, replacing unit-scale contraction. -/
theorem norm_parabolicDilate_le_max {c : ℝ} (hc : 0 ≤ c) (z : ParabolicSpace) :
    ‖parabolicDilate c z‖ ≤ max (c^2) c * ‖z‖ := by
  change max ‖c^2*z.1‖ ‖c • z.2‖ ≤ _
  simp only [norm_mul,norm_smul,Real.norm_eq_abs,abs_of_nonneg hc,
    abs_of_nonneg (sq_nonneg c)]
  apply max_le
  · exact (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg z.1)).trans
      (mul_le_mul_of_nonneg_left (norm_fst_le z) (le_max_of_le_right hc))
  · exact (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg z.2)).trans
      (mul_le_mul_of_nonneg_left (norm_snd_le z) (le_max_of_le_right hc))

/-- Actual dyadic factors have geometric support at every positive outer scale. -/
theorem dyadicKernelFactor_ae_norm_le_all (μ : Measure ParabolicSpace) {B T : ℝ}
    (hT : 0 ≤ T) (hsupp : ∀ᵐ z ∂μ, ‖z‖ ≤ B) (n : ℕ) :
    ∀ᵐ z ∂dyadicKernelFactor μ T n,
      ‖z‖ ≤ (max (T^2) T * B / 2) * (1/2 : ℝ)^n := by
  unfold dyadicKernelFactor
  apply (ae_map_iff (measurable_parabolicDilate _).aemeasurable
    (measurableSet_le continuous_norm.measurable measurable_const)).mpr
  filter_upwards [hsupp] with z hz
  have hp : 0 < (2 : ℝ)^(n+1) := by positivity
  have hsmall : 0 ≤ ((2 : ℝ)^(n+1))⁻¹ := inv_nonneg.mpr hp.le
  have hsmall1 : ((2 : ℝ)^(n+1))⁻¹ ≤ 1 :=
    (inv_le_one₀ hp).mpr (one_le_pow₀ (by norm_num))
  have hmap : parabolicDilate (T/2^(n+1)) z =
      parabolicDilate T (parabolicDilate ((2 : ℝ)^(n+1))⁻¹ z) := by
    rw [← parabolicDilate_mul,div_eq_mul_inv]
  rw [hmap]
  have hr := (norm_parabolicDilate_le_scale hsmall hsmall1 z).trans
    (mul_le_mul_of_nonneg_left hz hsmall)
  have hh := (norm_parabolicDilate_le_max hT _).trans
    (mul_le_mul_of_nonneg_left hr (le_max_of_le_right hT))
  have he : max (T^2) T * (((2 : ℝ)^(n+1))⁻¹ * B) =
      (max (T^2) T * B/2)*(1/2 : ℝ)^n := by
    rw [div_pow,one_pow,pow_succ]
    field_simp
    ring
  exact hh.trans_eq he

/-- The existing actual density converges at every positive scale. -/
theorem finiteKernelDensity_tendsto_all (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) :
    Tendsto (finiteKernelDensity Φ hΦ T hT) atTop (𝓝 (infiniteKernel Φ hΦ T hT)) := by
  have := kernelProfileMeasure_probability Φ hΦ
  obtain ⟨K,hK⟩ := compactSmoothSeed_lipschitz (scaledKernelProfile Φ (T/2))
    (scaledKernelProfile_smooth hΦ _) (scaledKernelProfile_compact hΦ (half_pos hT))
  exact convolutionIter_tendsto _ _ hK (by positivity : 0 ≤ max ((T/2)^2) (T/2)*1/2)
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ)<1)
    (dyadicKernelFactor_ae_norm_le_all _ (half_pos hT).le (kernelProfileMeasure_ae_norm_le Φ hΦ))

/-- Dilation covariance of the actual limit, with no upper scale restriction. -/
theorem infiniteKernel_dilate_all (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (x : ParabolicSpace) :
    infiniteKernel Φ hΦ T hT (parabolicDilate T x) =
      (T^5)⁻¹*infiniteKernel Φ hΦ 1 (by norm_num) x := by
  have ht := (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
    (finiteKernelDensity_tendsto_all Φ hΦ hT)).tendsto_at (parabolicDilate T x)
  have h1 := (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
    (finiteKernelDensity_tendsto Φ hΦ (by norm_num : (0 : ℝ)<1) le_rfl)).tendsto_at x
  apply tendsto_nhds_unique ht
  simpa only [finiteKernelDensity_dilate Φ hΦ hT] using h1.const_mul (T^5)⁻¹

/-- Unit-profile scaling without any upper bound on the source scale. -/
theorem infiniteKernel_eq_rescaled_unit_all (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (y : ParabolicSpace) :
    infiniteKernel Φ hΦ T hT y =
      (T^5)⁻¹*infiniteKernel Φ hΦ 1 (by norm_num) (parabolicDilate T⁻¹ y) := by
  simpa only [parabolicDilate_parabolicDilate_inv hT.ne'] using
    infiniteKernel_dilate_all Φ hΦ hT (parabolicDilate T⁻¹ y)

/-- Two arbitrary positive scales are related by the actual dilation map. -/
theorem infiniteKernel_scale_dilate (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {ℓ T : ℝ} (hℓ : 0 < ℓ) (hT : 0 < T) (y : ParabolicSpace) :
    infiniteKernel Φ hΦ (ℓ*T) (mul_pos hℓ hT) (parabolicDilate ℓ y) =
      (ℓ^5)⁻¹*infiniteKernel Φ hΦ T hT y := by
  rw [infiniteKernel_eq_rescaled_unit_all Φ hΦ (mul_pos hℓ hT),
    infiniteKernel_eq_rescaled_unit_all Φ hΦ hT, ← parabolicDilate_mul]
  have he : (ℓ*T)⁻¹*ℓ = T⁻¹ := by field_simp
  rw [he,mul_pow,mul_inv_rev]
  ring

end GlobalPhi43.MW20
