module

public import GlobalPhi43.MW20.ConvolutionLimit
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiating actual probability convolution

Uniformly bounded continuous derivative fields justify differentiation under
the integral. This is the analytic input for the smooth infinite kernel.
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- First derivatives commute with actual probability convolution. -/
theorem hasFDerivAt_probabilityConvolution (μ : Measure E) [IsProbabilityMeasure μ]
    (f : E →ᵇ F) (f' : E →ᵇ (E →L[ℝ] F))
    (hf : ∀ x, HasFDerivAt f (f' x) x) (x : E) :
    HasFDerivAt (probabilityConvolution μ f) (probabilityConvolution μ f' x) x := by
  change HasFDerivAt (fun z => ∫ y, f (z - y) ∂μ) (∫ y, f' (x - y) ∂μ) x
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := Set.univ)
    (F' := fun z y => f' (z - y)) (bound := fun _ => ‖f'‖) Filter.univ_mem
  · exact Eventually.of_forall fun z => (integrable_bounded_translate μ f z).aestronglyMeasurable
  · exact integrable_bounded_translate μ f x
  · exact (integrable_bounded_translate μ f' x).aestronglyMeasurable
  · exact ae_of_all μ fun y z _ => f'.norm_coe_le_norm (z - y)
  · exact integrable_const _
  · apply ae_of_all
    intro y z _
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using! (hf (z - y)).comp z ((hasFDerivAt_id z).sub_const y)

/-- Derivatives commute with every finite convolution average. -/
theorem convolutionIter_hasFDerivAt (μ : ℕ → Measure E) [∀ n, IsProbabilityMeasure (μ n)]
    (f : E →ᵇ F) (f' : E →ᵇ (E →L[ℝ] F))
    (hf : ∀ x, HasFDerivAt f (f' x) x) (n : ℕ) (x : E) :
    HasFDerivAt (convolutionIter μ f n) (convolutionIter μ f' n x) x := by
  induction n generalizing x with
  | zero => exact hf x
  | succ n ih =>
    exact hasFDerivAt_probabilityConvolution (μ n) _ _ ih x

end GlobalPhi43.MW20
