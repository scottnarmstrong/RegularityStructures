module

public import GlobalPhi43.MW20.CompactTestIntegral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Continuity of actual averages from local compact testing data
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory Filter Topology Set

variable {E F : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Continuity of an average needs only continuous germs on the compact
set actually reached by nearby tests. -/
theorem continuousAt_average_on_open (μ : Measure E) [IsFiniteMeasure μ]
    (f : E → F) {K U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (hf : ∀ w ∈ K, ContinuousAt f w)
    (htest : ∀ᵐ y ∂μ, ∀ z ∈ U, z + y ∈ K)
    {x : E} (hx : x ∈ U) : ContinuousAt (fun z => ∫ y, f (z + y) ∂μ) x := by
  have hcf : ContinuousOn f K := fun w hw => (hf w hw).continuousWithinAt
  obtain ⟨B, hB⟩ := (hK.image_of_continuousOn hcf.norm).bddAbove
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => |B|)
  · filter_upwards [hU.mem_nhds hx] with z hz
    have hmem : ∀ᵐ y ∂μ, z + y ∈ K := htest.mono fun y hy => hy z hz
    exact (integrable_comp_of_ae_mem_compact μ f hK hcf (fun y => z + y)
      (continuous_const.add continuous_id) hmem).aestronglyMeasurable
  · filter_upwards [hU.mem_nhds hx] with z hz
    filter_upwards [htest] with y hy
    exact (hB ⟨z + y, hy z hz, rfl⟩).trans (le_abs_self B)
  · exact integrable_const _
  · filter_upwards [htest] with y hy
    exact (hf _ (hy x hx)).tendsto.comp
      ((continuous_id.add continuous_const).continuousAt.tendsto)

end GlobalPhi43.MW20
