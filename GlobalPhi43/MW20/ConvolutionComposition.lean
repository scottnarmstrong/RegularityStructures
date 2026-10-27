module

public import GlobalPhi43.MW20.ConvolutionLinear
public import GlobalPhi43.MW20.KernelMeasure
public import Mathlib.MeasureTheory.Group.IntegralConvolution

/-!
# Composition of the actual probability averages
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory
open scoped BoundedContinuousFunction

variable {E F : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Composition is convolution of the probability measures. -/
theorem probabilityConvolution_conv (μ ν : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (f : E →ᵇ F) :
    probabilityConvolution (μ.conv ν) f = probabilityConvolution μ (probabilityConvolution ν f) := by
  ext x
  simp only [probabilityConvolution_apply]
  rw [integral_conv (integrable_bounded_translate (μ.conv ν) f x)]
  simp only [sub_add_eq_sub_sub]

/-- The averaging operators commute, including for the finite kernel factors. -/
theorem probabilityConvolution_comm (μ ν : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (f : E →ᵇ F) :
    probabilityConvolution μ (probabilityConvolution ν f) =
      probabilityConvolution ν (probabilityConvolution μ f) := by
  rw [← probabilityConvolution_conv, ← probabilityConvolution_conv]
  ext x
  simp only [probabilityConvolution_apply]
  rw [Measure.conv_comm]

end GlobalPhi43.MW20
