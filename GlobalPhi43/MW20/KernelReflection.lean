module

public import GlobalPhi43.MW20.KernelDensityIntegral
public import GlobalPhi43.MW20.InfiniteKernel

/-!
# Spatial reflection of the actual kernel factors
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Filter Topology
open scoped BoundedContinuousFunction

/-- Spatial reflection preserves Lebesgue integration in parabolic space. -/
theorem integral_spatialReflect (g : ParabolicSpace → ℝ) :
    (∫ y, g (parabolicDilate (-1) y)) = ∫ y, g y := by
  have hmap : volume.map (parabolicDilate (-1)) = (volume : Measure ParabolicSpace) := by
    simpa using (map_volume_parabolicDilate (d := -1) (by norm_num))
  have h := (parabolicKernelHomeomorph (-1) (by norm_num)).toMeasurableEquiv.measurableEmbedding.integral_map (μ := volume) g
  have heq : (parabolicKernelHomeomorph (-1) (by norm_num)).toMeasurableEquiv =
      (parabolicDilate (-1) : ParabolicSpace → ParabolicSpace) := by
    funext y
    exact parabolicKernelHomeomorph_apply (-1) (by norm_num) y
  simpa only [heq, hmap] using h.symm

/-- Spatial reflection preserves integration against every scaled factor. -/
theorem integral_scaledKernelMeasure_spatialReflect (Φ : ParabolicSpace → ℝ)
    (hΦ : KernelProfile Φ) {c : ℝ} (hc : 0 < c) (g : ParabolicSpace →ᵇ ℝ) :
    (∫ y, g (parabolicDilate (-1) y)
      ∂(kernelProfileMeasure Φ).map (parabolicDilate c)) =
    ∫ y, g y ∂(kernelProfileMeasure Φ).map (parabolicDilate c) := by
  have h := integral_scaledKernelMeasure Φ hΦ hc
    (g.compContinuous ⟨parabolicDilate (-1),
      (parabolicKernelHomeomorph (-1) (by norm_num)).continuous⟩)
  change (∫ y, g (parabolicDilate (-1) y)
    ∂(kernelProfileMeasure Φ).map (parabolicDilate c)) =
    ∫ y, scaledKernelProfile Φ c y * g (parabolicDilate (-1) y) at h
  rw [h, integral_scaledKernelMeasure Φ hΦ hc]
  have heven : ∀ y, scaledKernelProfile Φ c (parabolicDilate (-1) y) = scaledKernelProfile Φ c y := by
    intro y
    simp only [scaledKernelProfile, rescaledTestFunction, sub_zero, parabolicDilate,
      neg_one_sq, one_mul, neg_one_smul]
    rw [smul_neg, hΦ.spatial_even]
  have hi := integral_spatialReflect (fun y => scaledKernelProfile Φ c y * g y)
  simpa only [heven] using hi

end GlobalPhi43.MW20
