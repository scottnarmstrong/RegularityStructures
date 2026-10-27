module

public import GlobalPhi43.MW20.KernelReflection

/-!
# Spatial symmetry of the constructed finite and infinite kernels
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Filter Topology
open scoped BoundedContinuousFunction

/-- Every finite density retains the source's spatial symmetry. -/
theorem finiteKernelDensity_spatialReflect (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (n : ℕ) (x : ParabolicSpace) :
    finiteKernelDensity Φ hΦ T hT n (parabolicDilate (-1) x) =
      finiteKernelDensity Φ hΦ T hT n x := by
  have := kernelProfileMeasure_probability Φ hΦ
  induction n generalizing x with
  | zero =>
    simp only [finiteKernelDensity, convolutionIter, scaledKernelSeed_apply,
      parabolicDilate, neg_one_sq, one_mul, neg_one_smul, smul_neg, hΦ.spatial_even]
  | succ n ih =>
    change (∫ y, finiteKernelDensity Φ hΦ T hT n (parabolicDilate (-1) x - y)
      ∂(kernelProfileMeasure Φ).map (parabolicDilate (T / 2 / 2 ^ (n + 1)))) =
      ∫ y, finiteKernelDensity Φ hΦ T hT n (x - y)
        ∂(kernelProfileMeasure Φ).map (parabolicDilate (T / 2 / 2 ^ (n + 1)))
    have h := integral_scaledKernelMeasure_spatialReflect Φ hΦ
      (by positivity : 0 < T / 2 / 2 ^ (n + 1))
      ((finiteKernelDensity Φ hΦ T hT n).compContinuous
        ⟨fun y => parabolicDilate (-1) x - y, continuous_const.sub continuous_id⟩)
    change (∫ y, finiteKernelDensity Φ hΦ T hT n
      (parabolicDilate (-1) x - parabolicDilate (-1) y)
      ∂(kernelProfileMeasure Φ).map (parabolicDilate (T / 2 / 2 ^ (n + 1)))) = _ at h
    simp only [← parabolicDilate_sub, ih] at h
    exact h.symm

/-- Spatial symmetry passes to the uniform limit. -/
theorem infiniteKernel_spatialReflect (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) (x : ParabolicSpace) :
    infiniteKernel Φ hΦ T hT (parabolicDilate (-1) x) = infiniteKernel Φ hΦ T hT x := by
  have ht := (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
    (finiteKernelDensity_tendsto Φ hΦ hT hT1)).tendsto_at
  apply tendsto_nhds_unique (ht (parabolicDilate (-1) x))
  simpa only [finiteKernelDensity_spatialReflect Φ hΦ hT] using ht x

end GlobalPhi43.MW20
