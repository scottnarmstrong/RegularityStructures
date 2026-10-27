module

public import GlobalPhi43.Markov.FiniteDimensional
public import GlobalPhi43.Markov.FlowKernel

/-! # Finite-dimensional laws of the supplied flow witness -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory RegularityStructures
open scoped NNReal

namespace GlobalPhi43.Markov

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Time sections of the measurable sampled flow law. -/
def flowObservationKernel (P : Measure Ω) [SFinite P] {η : NegExponent}
    (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η)
    (hm : Measurable (fun q : (ℝ≥0 × HolderBesov η) × Ω => u q.1.1 0 q.1.2 q.2))
    (t : ℝ≥0) : Kernel (HolderBesov η) (HolderBesov η) :=
  (sampleKernel P (fun q => u q.1.1 0 q.1.2 q.2) hm).comap (fun x => (t, x))
    measurable_prodMk_left

instance flowObservationKernel_isMarkov (P : Measure Ω) [IsProbabilityMeasure P]
    {η : NegExponent} (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η)
    (hm : Measurable (fun q : (ℝ≥0 × HolderBesov η) × Ω => u q.1.1 0 q.1.2 q.2))
    (t : ℝ≥0) : IsMarkovKernel (flowObservationKernel P u hm t) := by
  unfold flowObservationKernel
  infer_instance

end GlobalPhi43.Markov
