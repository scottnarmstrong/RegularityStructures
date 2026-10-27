module

public import GlobalPhi43.MW20.ConvolutionLimit
public import GlobalPhi43.MW20.DyadicKernelMeasure
public import RegularityStructures.Analysis.Parabolic.TestFunction

/-!
# Infinite averages of the actual parabolically scaled kernel measures
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Filter Topology
open scoped BoundedContinuousFunction NNReal

/-- For scales at most one, the ordinary norm contracts by the spatial scale. -/
theorem norm_parabolicDilate_le_scale {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (z : ParabolicSpace) : ‖parabolicDilate c z‖ ≤ c * ‖z‖ := by
  change max ‖c ^ 2 * z.1‖ ‖c • z.2‖ ≤ c * ‖z‖
  simp only [norm_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc,
    abs_of_nonneg (sq_nonneg c)]
  apply max_le
  · exact (mul_le_mul_of_nonneg_right (by nlinarith : c ^ 2 ≤ c) (abs_nonneg z.1)).trans
      (mul_le_mul_of_nonneg_left (norm_fst_le z) hc)
  · exact mul_le_mul_of_nonneg_left (norm_snd_le z) hc

/-- The support of each pushed-forward measure has the summably shrinking radius. -/
theorem dyadicKernelFactor_ae_norm_le (μ : Measure ParabolicSpace) {B T : ℝ}
    (hT : 0 ≤ T) (hT1 : T ≤ 1) (hsupp : ∀ᵐ z ∂μ, ‖z‖ ≤ B) (n : ℕ) :
    ∀ᵐ z ∂dyadicKernelFactor μ T n, ‖z‖ ≤ (T * B / 2) * (1 / 2 : ℝ) ^ n := by
  have hp : 0 < (2 : ℝ) ^ (n + 1) := by positivity
  have hc : 0 ≤ T / (2 : ℝ) ^ (n + 1) := div_nonneg hT hp.le
  have hc1 : T / (2 : ℝ) ^ (n + 1) ≤ 1 :=
    (div_le_one hp).2 (hT1.trans (one_le_pow₀ (by norm_num)))
  unfold dyadicKernelFactor
  apply (ae_map_iff (measurable_parabolicDilate _).aemeasurable
    (measurableSet_le continuous_norm.measurable measurable_const)).2
  filter_upwards [hsupp] with z hz
  have hbound := (norm_parabolicDilate_le_scale hc hc1 z).trans
    (mul_le_mul_of_nonneg_left hz hc)
  have heq : T / (2 : ℝ) ^ (n + 1) * B = (T * B / 2) * (1 / 2 : ℝ) ^ n := by
    rw [pow_succ, div_pow]
    simp only [one_pow]
    ring
  exact heq ▸ hbound

/-- Existence of the infinite dyadic average for every bounded Lipschitz seed.
The radius estimate is proved for the actual parabolic pushforwards above. -/
theorem dyadic_convolutionIter_tendsto {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure ParabolicSpace) [IsProbabilityMeasure μ] (f : ParabolicSpace →ᵇ F)
    {K : ℝ≥0} (hf : LipschitzWith K f) {B T : ℝ} (hB : 0 ≤ B)
    (hT : 0 ≤ T) (hT1 : T ≤ 1) (hsupp : ∀ᵐ z ∂μ, ‖z‖ ≤ B) :
    Tendsto (convolutionIter (dyadicKernelFactor μ T) f) atTop
      (𝓝 (convolutionLimit (dyadicKernelFactor μ T) f)) := by
  exact convolutionIter_tendsto _ f hf (by positivity : 0 ≤ T * B / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    (dyadicKernelFactor_ae_norm_le μ hT hT1 hsupp)

end GlobalPhi43.MW20
