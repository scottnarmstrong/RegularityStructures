module

public import GlobalPhi43.Compactness.Embedding
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.Topology.Sequences

/-! # The tightness-to-subsequence bridge for the invariant-measure argument -/

public noncomputable section

open MeasureTheory Filter Set Topology

namespace GlobalPhi43.Invariant

variable {E : Type*} [TopologicalSpace E] [PolishSpace E]
  [MeasurableSpace E] [BorelSpace E]

/-- A tight sequence has an actual strictly increasing weakly convergent subsequence.
The limit is a probability measure on the original Borel state space. -/
theorem exists_tendsto_subseq_of_tight (μ : ℕ → ProbabilityMeasure E)
    (hμ : IsTightMeasureSet (Set.range fun n => (μ n : Measure E))) :
    ∃ ν : ProbabilityMeasure E, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (μ ∘ φ) atTop (𝓝 ν) := by
  have ht : IsTightMeasureSet
      {((ν : ProbabilityMeasure E) : Measure E) | ν ∈ Set.range μ} := by
    convert hμ using 1
    ext ν
    simp only [Set.mem_ofPred_eq, Set.mem_range, exists_exists_eq_and]
  obtain ⟨ν, _, φ, hφ, hlim⟩ :=
    (isCompact_closure_of_isTightMeasureSet ht).tendsto_subseq
      (fun n => subset_closure (Set.mem_range_self n))
  exact ⟨ν, φ, hφ, hlim⟩

end GlobalPhi43.Invariant
