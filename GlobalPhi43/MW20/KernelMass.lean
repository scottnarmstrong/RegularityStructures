module

public import GlobalPhi43.MW20.FiniteKernelDensityMeasure
public import GlobalPhi43.MW20.KernelPositivity

/-!
# Unit mass of the constructed kernel densities
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Filter Topology
open scoped BoundedContinuousFunction

/-- Each actual finite convolution has unit mass. -/
theorem integral_finiteKernelDensity (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) (n : ℕ) :
    (∫ x, finiteKernelDensity Φ hΦ T hT n x) = 1 := by
  have := kernelProfileMeasure_probability Φ hΦ
  simpa only [BoundedContinuousFunction.const_apply, mul_one, integral_const,
    Measure.real, measure_univ, ENNReal.toReal_one, one_smul] using
    integral_finiteKernelDensity_mul Φ hΦ hT hT1 n
      (BoundedContinuousFunction.const ParabolicSpace (1 : ℝ))

/-- Uniform convergence with common compact support preserves unit mass. -/
theorem integral_infiniteKernel (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) :
    (∫ x, infiniteKernel Φ hΦ T hT x) = 1 := by
  let S := Metric.closedBall (0 : ParabolicSpace) T
  have hS : IsCompact S := isCompact_closedBall _ _
  have : IsFiniteMeasure (volume.restrict S) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hS.measure_lt_top⟩
  have hfinite : ∀ n, (∫ x in S, finiteKernelDensity Φ hΦ T hT n x) = 1 := by
    intro n
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact integral_finiteKernelDensity Φ hΦ hT hT1 n
    · intro x hx
      exact finiteKernelDensity_eq_zero_of_norm_gt Φ hΦ hT hT1 n
        (by simpa only [S, Metric.mem_closedBall, dist_zero_right, not_le] using hx)
  have hlim := (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
    (finiteKernelDensity_tendsto Φ hΦ hT hT1)).tendsto_at
  have ht : Tendsto (fun n => ∫ x in S, finiteKernelDensity Φ hΦ T hT n x) atTop
      (𝓝 (∫ x in S, infiniteKernel Φ hΦ T hT x)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun _ => ‖scaledKernelSeed Φ hΦ (T / 2) (half_pos hT)‖)
    · exact fun n => (finiteKernelDensity Φ hΦ T hT n).continuous.aestronglyMeasurable
    · exact integrable_const _
    · intro n
      exact ae_of_all _ fun x =>
        ((finiteKernelDensity Φ hΦ T hT n).norm_coe_le_norm x).trans
          (norm_finiteKernelDensity_le Φ hΦ hT n)
    · exact ae_of_all _ hlim
  have heq : (∫ x in S, infiniteKernel Φ hΦ T hT x) = 1 := by
    apply tendsto_nhds_unique ht
    simpa only [hfinite] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero] at heq
  · exact heq
  · intro x hx
    exact infiniteKernel_eq_zero_of_norm_gt Φ hΦ hT hT1
      (by simpa only [S, Metric.mem_closedBall, dist_zero_right, not_le] using hx)

end GlobalPhi43.MW20
