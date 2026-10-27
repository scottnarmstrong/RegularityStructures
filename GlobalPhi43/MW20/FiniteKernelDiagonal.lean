module

public import GlobalPhi43.MW20.DyadicKernelSupport
public import GlobalPhi43.MW20.FiniteSmoothing
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Integrability of continuous sections against the compactly supported finite dyadic kernels. -/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Local Set

/-- Every continuous field can be tested against the actual finite kernels.
Only its values on a compact neighbourhood of the evaluation point enter. -/
theorem integrable_dyadic_section (μ : Measure ParabolicSpace)
    [IsProbabilityMeasure μ] {T : ℝ} (hT : 0 ≤ T)
    (hμ : ∀ᵐ z ∂μ, z.1 ≤ 0 ∧ pdist 0 z ≤ 1)
    (n : ℕ) (f : ParabolicSpace → ℝ) (hf : Continuous f) (x : ParabolicSpace) :
    Integrable (fun z => f (x + z)) (dyadicKernelMeasure μ T n) := by
  have hc : Continuous (fun z => f (x + z)) :=
    hf.comp (continuous_const.add continuous_id)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ParabolicSpace) (max (T ^ 2) T)).exists_bound_of_continuousOn hc.continuousOn
  apply Integrable.of_bound hc.aestronglyMeasurable C
  filter_upwards [dyadicKernelMeasure_ae_norm_le μ hT hμ n] with z hz
  exact hC z (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz)

end GlobalPhi43.MW20
