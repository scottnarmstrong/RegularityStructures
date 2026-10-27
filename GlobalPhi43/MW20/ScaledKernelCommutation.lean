module

public import GlobalPhi43.MW20.KernelDensityIntegral
public import GlobalPhi43.MW20.ProbabilityConvolution
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Commutativity of the actual scaled density factors
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures
open scoped BoundedContinuousFunction

/-- The first two density factors can be interchanged, with their exact
parabolic normalizations. -/
theorem probabilityConvolution_scaledSeeds_comm (Φ : ParabolicSpace → ℝ)
    (hΦ : KernelProfile Φ) {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    letI := kernelProfileMeasure_probability Φ hΦ
    probabilityConvolution ((kernelProfileMeasure Φ).map (parabolicDilate c))
      (scaledKernelSeed Φ hΦ d hd) =
    probabilityConvolution ((kernelProfileMeasure Φ).map (parabolicDilate d))
      (scaledKernelSeed Φ hΦ c hc) := by
  have := kernelProfileMeasure_probability Φ hΦ
  have : Measure.IsAddHaarMeasure (volume : Measure ParabolicSpace) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  ext x
  simp only [probabilityConvolution_apply, scaledKernelSeed_apply]
  have hleft := integral_scaledKernelMeasure Φ hΦ hc
    ((scaledKernelSeed Φ hΦ d hd).compContinuous
      ⟨fun y => x - y, continuous_const.sub continuous_id⟩)
  have hright := integral_scaledKernelMeasure Φ hΦ hd
    ((scaledKernelSeed Φ hΦ c hc).compContinuous
      ⟨fun y => x - y, continuous_const.sub continuous_id⟩)
  simp only [BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk,
    scaledKernelSeed_apply] at hleft hright
  rw [hleft, hright]
  rw [← integral_sub_left_eq_self _ volume x]
  simp only [sub_sub_cancel, scaledKernelProfile, rescaledTestFunction, sub_zero]
  apply integral_congr_ae
  exact ae_of_all _ fun y => by ring

end GlobalPhi43.MW20
