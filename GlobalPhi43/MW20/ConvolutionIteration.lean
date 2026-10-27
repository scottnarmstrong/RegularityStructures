module

public import GlobalPhi43.MW20.ConvolutionComposition
public import GlobalPhi43.MW20.ConvolutionLimit

/-!
# Rearranging finite probability averages
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory
open scoped BoundedContinuousFunction

variable {E F : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Remove the first factor from the finite iteration. -/
theorem convolutionIter_shift (μ : ℕ → Measure E) [∀ n, IsProbabilityMeasure (μ n)]
    (f : E →ᵇ F) (n : ℕ) :
    convolutionIter μ f (n + 1) =
      convolutionIter (fun j => μ (j + 1)) (probabilityConvolution (μ 0) f) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change probabilityConvolution (μ (n + 1)) (convolutionIter μ f (n + 1)) = _
    exact congrArg (probabilityConvolution (μ (n + 1))) ih

/-- An external probability average commutes with every finite iteration. -/
theorem convolutionIter_probabilityConvolution (μ : ℕ → Measure E)
    [∀ n, IsProbabilityMeasure (μ n)] (ν : Measure E) [IsProbabilityMeasure ν]
    (f : E →ᵇ F) (n : ℕ) :
    convolutionIter μ (probabilityConvolution ν f) n =
      probabilityConvolution ν (convolutionIter μ f n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [convolutionIter_succ, ih]
    exact probabilityConvolution_comm _ _ _

end GlobalPhi43.MW20
