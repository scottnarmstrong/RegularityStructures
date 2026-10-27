module

public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Topology.Order.Compact

/-!
# Integrability from local continuity on the actual compact testing set
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory Set

variable {E F : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [NormedAddCommGroup F]

/-- A continuous sampling map into a compact testing set needs no global
continuity or measurability of the sampled field outside that set. -/
theorem integrable_comp_of_ae_mem_compact (μ : Measure E) [IsFiniteMeasure μ]
    (f : E → F) {K : Set E} (hK : IsCompact K) (hf : ContinuousOn f K)
    (g : E → E) (hg : Continuous g) (hmem : ∀ᵐ y ∂μ, g y ∈ K) :
    Integrable (fun y => f (g y)) μ := by
  have hS : MeasurableSet (g ⁻¹' K) := (hK.isClosed.preimage hg).measurableSet
  have hc : ContinuousOn (fun y => f (g y)) (g ⁻¹' K) :=
    hf.comp hg.continuousOn (fun _ hy => hy)
  have hm := hc.aestronglyMeasurable (μ := μ) hS
  rw [Measure.restrict_eq_self_of_ae_mem (s := g ⁻¹' K) hmem] at hm
  obtain ⟨B, hB⟩ := (hK.image_of_continuousOn hf.norm).bddAbove
  apply (integrable_const B).mono' hm
  filter_upwards [hmem] with y hy
  exact hB ⟨g y, hy, rfl⟩

end GlobalPhi43.MW20
