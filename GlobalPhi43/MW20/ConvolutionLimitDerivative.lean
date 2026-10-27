module

public import GlobalPhi43.MW20.ConvolutionDerivative
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-!
# Derivatives of the constructed infinite convolution average
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The limit has the limit derivative, both constructed from the actual
finite averages. No derivative-convergence hypothesis is added: it follows
from the shrinking measures and the Lipschitz estimates of the two seeds. -/
theorem hasFDerivAt_convolutionLimit (μ : ℕ → Measure E) [∀ n, IsProbabilityMeasure (μ n)]
    (f : E →ᵇ F) (f' : E →ᵇ (E →L[ℝ] F))
    (hf : ∀ x, HasFDerivAt f (f' x) x) {K K' : ℝ≥0}
    (hLip : LipschitzWith K f) (hLip' : LipschitzWith K' f')
    {A q : ℝ} (hA : 0 ≤ A) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hsupp : ∀ n, ∀ᵐ y ∂μ n, ‖y‖ ≤ A * q ^ n) (x : E) :
    HasFDerivAt (convolutionLimit μ f) (convolutionLimit μ f' x) x := by
  have hlim := convolutionIter_tendsto μ f hLip hA hq0 hq1 hsupp
  have hlim' := convolutionIter_tendsto μ f' hLip' hA hq0 hq1 hsupp
  have hu := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hlim
  have hu' := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hlim'
  exact hasFDerivAt_of_tendstoUniformly hu' (convolutionIter_hasFDerivAt μ f f' hf)
    (fun y => hu.tendsto_at y) x

end GlobalPhi43.MW20
