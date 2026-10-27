module

public import GlobalPhi43.MW20.FiniteKernelDiagonal
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Integrability of continuous functions against probability measures supported on a compact set. -/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Local Set Filter
open scoped Topology

/-- A continuous field is integrable against a finite measure concentrated on
one compact set. This is used for the varying outer kernels. -/
theorem integrable_of_continuous_compact_ae (ν : Measure ParabolicSpace)
    [IsFiniteMeasure ν] (s : Set ParabolicSpace) (hs : IsCompact s)
    (hν : ∀ᵐ x ∂ν, x ∈ s) (f : ParabolicSpace → ℝ) (hf : Continuous f) :
    Integrable f ν := by
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuousOn hf.continuousOn
  apply Integrable.of_bound hf.aestronglyMeasurable C
  filter_upwards [hν] with x hx
  exact hC x hx

end GlobalPhi43.MW20
