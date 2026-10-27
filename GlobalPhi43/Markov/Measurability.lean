module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.Topology.MetricSpace.Polish

public section

open MeasureTheory TopologicalSpace

namespace GlobalPhi43.Markov

/-- Generic Caratheodory step: fixed-window sections give product measurability.
No measurability in a time parameter is inferred here. -/
theorem measurable_joint_of_sections {E Ω Y : Type*}
    [MetricSpace E] [SeparableSpace E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace Ω] [PseudoMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {F : E → Ω → Y} (hc : ∀ ω, Continuous fun x => F x ω)
    (hm : ∀ x, Measurable (F x)) : Measurable (fun p : E × Ω => F p.1 p.2) :=
  measurable_uncurry_of_continuous_of_measurable hc hm

end GlobalPhi43.Markov
