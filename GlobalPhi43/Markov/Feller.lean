module

public import GlobalPhi43.Markov.Samples
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.ContinuousMap.Bounded.Basic

public noncomputable section

open MeasureTheory Set Filter Topology
open scoped BoundedContinuousFunction

namespace GlobalPhi43.Markov

variable {A Ω E : Type*} [TopologicalSpace A] [FirstCountableTopology A]
  [MeasurableSpace Ω] [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- Bounded-continuous observables have continuous expectations under almost-sure parameter
continuity. The parameter can be the initial datum or time. -/
theorem continuous_sample_expectation {F : A → Ω → E}
    (hm : ∀ a, Measurable (F a)) (hc : ∀ᵐ ω ∂P, Continuous (fun a => F a ω))
    (f : E →ᵇ ℝ) : Continuous (fun a => ∫ ω, f (F a ω) ∂P) := by
  apply continuous_of_dominated (bound := fun _ => ‖f‖)
  · intro a
    exact (f.continuous.measurable.comp (hm a)).aestronglyMeasurable
  · intro a
    exact Eventually.of_forall fun ω => f.norm_coe_le_norm (F a ω)
  · exact integrable_const _
  · filter_upwards [hc] with ω hω
    exact f.continuous.comp hω

omit [TopologicalSpace A] [FirstCountableTopology A] [MeasurableSpace E] [BorelSpace E] in
/-- Kernel expectation preserves the supremum bound, with constant one. -/
theorem abs_sample_expectation_le (F : A → Ω → E) (f : E →ᵇ ℝ) (a : A) :
    |∫ ω, f (F a ω) ∂P| ≤ ‖f‖ := by
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := P)
      (Eventually.of_forall fun ω => f.norm_coe_le_norm (F a ω))

end GlobalPhi43.Markov
