module

public import GlobalPhi43.MW20.ProbabilityConvolution
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Constructing an infinite convolution average in uniform norm

The input measures have summably shrinking support. Convergence is proved
from their actual integrals and a Lipschitz seed, not supplied as a field.
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction NNReal

variable {E F : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The successive finite averages, with zero steps equal to the seed. -/
@[expose] noncomputable def convolutionIter (μ : ℕ → Measure E)
    [∀ n, IsProbabilityMeasure (μ n)] (f : E →ᵇ F) : ℕ → E →ᵇ F
  | 0 => f
  | n + 1 => probabilityConvolution (μ n) (convolutionIter μ f n)

@[simp] theorem convolutionIter_succ (μ : ℕ → Measure E) [∀ n, IsProbabilityMeasure (μ n)]
    (f : E →ᵇ F) (n : ℕ) : convolutionIter μ f (n + 1) =
      probabilityConvolution (μ n) (convolutionIter μ f n) := rfl

/-- All finite convolutions retain the Lipschitz bound of the first factor. -/
theorem convolutionIter_lipschitz (μ : ℕ → Measure E) [∀ n, IsProbabilityMeasure (μ n)]
    (f : E →ᵇ F) {K : ℝ≥0} (hf : LipschitzWith K f) (n : ℕ) :
    LipschitzWith K (convolutionIter μ f n) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact lipschitz_probabilityConvolution (μ n) _ ih

variable [CompleteSpace F]

/-- Actual finite averages have the summable increment estimate. -/
theorem convolutionIter_increment (μ : ℕ → Measure E) [∀ n, IsProbabilityMeasure (μ n)]
    (f : E →ᵇ F) {K : ℝ≥0} (hf : LipschitzWith K f) {r : ℝ} (hr : 0 ≤ r)
    (n : ℕ) (hsupp : ∀ᵐ y ∂μ n, ‖y‖ ≤ r) :
    ‖convolutionIter μ f (n + 1) - convolutionIter μ f n‖ ≤ (K : ℝ) * r :=
  norm_probabilityConvolution_sub_le (μ n) _ (convolutionIter_lipschitz μ f hf n) hr hsupp

/-- Geometrically shrinking measures produce a Cauchy sequence in uniform norm. -/
theorem convolutionIter_cauchy (μ : ℕ → Measure E) [∀ n, IsProbabilityMeasure (μ n)]
    (f : E →ᵇ F) {K : ℝ≥0} (hf : LipschitzWith K f)
    {A q : ℝ} (hA : 0 ≤ A) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hsupp : ∀ n, ∀ᵐ y ∂μ n, ‖y‖ ≤ A * q ^ n) : CauchySeq (convolutionIter μ f) := by
  apply SeminormedAddCommGroup.cauchySeq_of_le_geometric (C := (K : ℝ) * A) hq1
  intro n
  have hi := convolutionIter_increment μ f hf (mul_nonneg hA (pow_nonneg hq0 n)) n (hsupp n)
  rw [norm_sub_rev]
  simpa only [mul_assoc] using hi

/-- The constructed infinite convolution average. Its convergence is proved below. -/
@[expose] noncomputable def convolutionLimit (μ : ℕ → Measure E)
    [∀ n, IsProbabilityMeasure (μ n)] (f : E →ᵇ F) : E →ᵇ F :=
  limUnder atTop (convolutionIter μ f)

/-- Existence and uniform-norm convergence of the infinite average. -/
theorem convolutionIter_tendsto (μ : ℕ → Measure E) [∀ n, IsProbabilityMeasure (μ n)]
    (f : E →ᵇ F) {K : ℝ≥0} (hf : LipschitzWith K f)
    {A q : ℝ} (hA : 0 ≤ A) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hsupp : ∀ n, ∀ᵐ y ∂μ n, ‖y‖ ≤ A * q ^ n) :
    Tendsto (convolutionIter μ f) atTop (𝓝 (convolutionLimit μ f)) :=
  (convolutionIter_cauchy μ f hf hA hq0 hq1 hsupp).tendsto_limUnder

end GlobalPhi43.MW20
