module

public import GlobalPhi43.MW20.ConvolutionLimit
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Linear postcomposition commutes with finite and infinite probability averages
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction NNReal

variable {E F G : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- Linear maps commute with the actual averaging integral. -/
theorem probabilityConvolution_postcompose (μ : Measure E) [IsProbabilityMeasure μ]
    (L : F →L[ℝ] G) (f : E →ᵇ F) :
    probabilityConvolution μ (L.compLeftContinuousBounded E f) =
      L.compLeftContinuousBounded E (probabilityConvolution μ f) := by
  ext x
  exact L.integral_comp_comm (integrable_bounded_translate μ f x)

/-- The finite identity holds at every convolution depth. -/
theorem convolutionIter_postcompose (μ : ℕ → Measure E) [∀ n, IsProbabilityMeasure (μ n)]
    (L : F →L[ℝ] G) (f : E →ᵇ F) (n : ℕ) :
    convolutionIter μ (L.compLeftContinuousBounded E f) n =
      L.compLeftContinuousBounded E (convolutionIter μ f n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [convolutionIter_succ, ih, probabilityConvolution_postcompose]; rfl


/-- Linear maps commute with the constructed limit, by norm convergence. -/
theorem convolutionLimit_postcompose (μ : ℕ → Measure E) [∀ n, IsProbabilityMeasure (μ n)]
    (L : F →L[ℝ] G) (f : E →ᵇ F) {K : ℝ≥0} (hf : LipschitzWith K f)
    {A q : ℝ} (hA : 0 ≤ A) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hsupp : ∀ n, ∀ᵐ y ∂μ n, ‖y‖ ≤ A * q ^ n) :
    convolutionLimit μ (L.compLeftContinuousBounded E f) =
      L.compLeftContinuousBounded E (convolutionLimit μ f) := by
  have hlim := convolutionIter_tendsto μ f hf hA hq0 hq1 hsupp
  have hLf : LipschitzWith (‖L‖₊ * K) (L.compLeftContinuousBounded E f) := L.lipschitzWith.comp hf
  have hlimL := convolutionIter_tendsto μ (L.compLeftContinuousBounded E f) hLf hA hq0 hq1 hsupp
  have hcomp := ((L.compLeftContinuousBounded E).continuous.tendsto (convolutionLimit μ f)).comp hlim
  have hcomp' : Tendsto (convolutionIter μ (L.compLeftContinuousBounded E f)) atTop
      (𝓝 (L.compLeftContinuousBounded E (convolutionLimit μ f))) := by
    convert! hcomp using 1
    funext n
    exact convolutionIter_postcompose μ L f n
  exact tendsto_nhds_unique hlimL hcomp'

end GlobalPhi43.MW20
