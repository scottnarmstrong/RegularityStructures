module

public import GlobalPhi43.Invariant.Portmanteau
public import GlobalPhi43.Invariant.LateMoments
public import Mathlib.Topology.Semicontinuity.Basic

/-! # All supplied moment profiles attach to one already selected weak limit -/

public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace GlobalPhi43.Invariant

variable {E : Type*} [TopologicalSpace E] [PolishSpace E]
  [MeasurableSpace E] [BorelSpace E]

/-- No new subsequence is chosen for the observable or its real exponent. -/
theorem weakLimit_moment_le {ν : ℕ → ProbabilityMeasure E} {μ : ProbabilityMeasure E}
    (hμ : Tendsto ν atTop (𝓝 μ)) {N : E → ℝ≥0∞} (hN : LowerSemicontinuous N)
    {p : ℝ} (hp : 0 ≤ p) {C : ℝ≥0∞}
    (hC : ∀ n, ∫⁻ z, N z ^ p ∂(ν n : Measure E) ≤ C) :
    ∫⁻ z, N z ^ p ∂(μ : Measure E) ≤ C := by
  have hg : LowerSemicontinuous (fun z => N z ^ p) :=
    ENNReal.continuous_rpow_const.comp_lowerSemicontinuous hN
      (fun _ _ h => ENNReal.rpow_le_rpow h hp)
  exact (lintegral_le_liminf_of_tendsto hμ hg).trans
    (by simpa using Filter.liminf_le_liminf (f := atTop) (Eventually.of_forall hC))

/-- Quantitative heat-probe moments on the original state space. -/
theorem holderBesov_weakLimit_moment_le (η : RegularityStructures.NegExponent)
    {ν : ℕ → ProbabilityMeasure (RegularityStructures.HolderBesov η)}
    {μ : ProbabilityMeasure (RegularityStructures.HolderBesov η)}
    (hμ : Tendsto ν atTop (𝓝 μ)) (α : ℝ) {p : ℝ} (hp : 0 ≤ p)
    {C : ℝ≥0∞}
    (hC : ∀ n, ∫⁻ z, extNorm η α z ^ p ∂(ν n : Measure _) ≤ C) :
    ∫⁻ z, extNorm η α z ^ p ∂(μ : Measure _) ≤ C :=
  weakLimit_moment_le hμ (lowerSemicontinuous_extNorm η α) hp hC

end GlobalPhi43.Invariant
