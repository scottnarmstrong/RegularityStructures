module

public import GlobalPhi43.MW20.ProbabilityConvolution

/-!
# Probability convolution as a continuous linear contraction
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory
open scoped BoundedContinuousFunction

variable {E F : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Addition commutes with averaging against a probability measure. -/
theorem probabilityConvolution_add (μ : Measure E) [IsProbabilityMeasure μ] (f g : E →ᵇ F) :
    probabilityConvolution μ (f + g) = probabilityConvolution μ f + probabilityConvolution μ g := by
  ext x
  exact integral_add (integrable_bounded_translate μ f x) (integrable_bounded_translate μ g x)

/-- Scalar multiplication commutes with averaging. -/
theorem probabilityConvolution_smul (μ : Measure E) [IsProbabilityMeasure μ]
    (c : ℝ) (f : E →ᵇ F) : probabilityConvolution μ (c • f) = c • probabilityConvolution μ f := by
  ext x
  exact integral_smul c _

/-- The actual integral operator, as a continuous linear contraction. -/
@[expose] noncomputable def probabilityConvolutionCLM (μ : Measure E) [IsProbabilityMeasure μ] :
    (E →ᵇ F) →L[ℝ] (E →ᵇ F) :=
  LinearMap.mkContinuous
    { toFun := probabilityConvolution μ
      map_add' := probabilityConvolution_add μ
      map_smul' := probabilityConvolution_smul μ }
    1 (fun f => by simpa using norm_probabilityConvolution_le μ f)

end GlobalPhi43.MW20
