module

public import GlobalPhi43.MW20.LocalAverageDerivative

/-!
# Local first and second derivatives of the actual averages
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory Filter Topology Set
open scoped ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- An open testing set lets the derivative formula hold at each of its
points, using a smaller ball there. -/
theorem hasFDerivAt_average_on_open (μ : Measure E) [IsFiniteMeasure μ]
    (f : E → F) {K U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (hf : ∀ w ∈ K, ContDiffAt ℝ 1 f w)
    (htest : ∀ᵐ y ∂μ, ∀ z ∈ U, z + y ∈ K)
    {x : E} (hx : x ∈ U) :
    HasFDerivAt (fun z => ∫ y, f (z + y) ∂μ)
      (∫ y, fderiv ℝ f (x + y) ∂μ) x := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  apply hasFDerivAt_local_average μ f hK hf x hδ
  filter_upwards [htest] with y hy
  exact fun z hz => hy z (hball hz)

/-- The actual second derivative is obtained by averaging the actual second
derivative on the compact testing neighbourhood. -/
theorem hasFDerivAt_fderiv_average_on_open (μ : Measure E) [IsFiniteMeasure μ]
    (f : E → F) {K U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (hf : ∀ w ∈ K, ContDiffAt ℝ 2 f w)
    (htest : ∀ᵐ y ∂μ, ∀ z ∈ U, z + y ∈ K)
    {x : E} (hx : x ∈ U) :
    HasFDerivAt (fderiv ℝ (fun z => ∫ y, f (z + y) ∂μ))
      (∫ y, fderiv ℝ (fderiv ℝ f) (x + y) ∂μ) x := by
  have hf1 : ∀ w ∈ K, ContDiffAt ℝ 1 f w := fun w hw => (hf w hw).of_le (by norm_num)
  have hd1 : ∀ w ∈ K, ContDiffAt ℝ 1 (fderiv ℝ f) w := fun w hw =>
    (hf w hw).fderiv_right (m := 1) (by norm_num)
  have hsecond := hasFDerivAt_average_on_open μ (fderiv ℝ f) hK hU hd1 htest hx
  apply hsecond.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hx] with z hz
  exact (hasFDerivAt_average_on_open μ f hK hU hf1 htest hz).fderiv

end GlobalPhi43.MW20
