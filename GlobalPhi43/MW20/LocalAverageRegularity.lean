module

public import GlobalPhi43.MW20.LocalAverageSecondDerivative
public import GlobalPhi43.MW20.LocalAverageContinuity

/-!
# Classical regularity of averages from local compact testing germs
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory Filter Topology Set
open scoped ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- C¹ germs on the actual compact testing tube give a C¹ average. -/
theorem contDiffAt_average_on_open_one (μ : Measure E) [IsFiniteMeasure μ]
    (f : E → F) {K U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (hf : ∀ w ∈ K, ContDiffAt ℝ 1 f w)
    (htest : ∀ᵐ y ∂μ, ∀ z ∈ U, z + y ∈ K)
    {x : E} (hx : x ∈ U) : ContDiffAt ℝ 1 (fun z => ∫ y, f (z + y) ∂μ) x := by
  apply (contDiffAt_succ_iff_hasFDerivAt (n := 0)).mpr
  refine ⟨fun z => ∫ y, fderiv ℝ f (z + y) ∂μ, ⟨U, hU.mem_nhds hx, ?_⟩, ?_⟩
  · intro z hz
    exact hasFDerivAt_average_on_open μ f hK hU hf htest hz
  · apply contDiffAt_zero.mpr
    refine ⟨U, hU.mem_nhds hx, ?_⟩
    intro z hz
    exact (continuousAt_average_on_open μ (fderiv ℝ f) hK hU
      (fun w hw => (hf w hw).continuousAt_fderiv one_ne_zero) htest hz).continuousWithinAt

/-- Local C² source data produce actual C² averages, without a smoothness
hypothesis on the average or outside the compact testing tube. -/
theorem contDiffAt_average_on_open_two (μ : Measure E) [IsFiniteMeasure μ]
    (f : E → F) {K U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (hf : ∀ w ∈ K, ContDiffAt ℝ 2 f w)
    (htest : ∀ᵐ y ∂μ, ∀ z ∈ U, z + y ∈ K)
    {x : E} (hx : x ∈ U) : ContDiffAt ℝ 2 (fun z => ∫ y, f (z + y) ∂μ) x := by
  apply (contDiffAt_succ_iff_hasFDerivAt (n := 1)).mpr
  refine ⟨fun z => ∫ y, fderiv ℝ f (z + y) ∂μ, ⟨U, hU.mem_nhds hx, ?_⟩, ?_⟩
  · intro z hz
    exact hasFDerivAt_average_on_open μ f hK hU
      (fun w hw => (hf w hw).of_le (by norm_num)) htest hz
  · exact contDiffAt_average_on_open_one μ (fderiv ℝ f) hK hU
      (fun w hw => (hf w hw).fderiv_right (m := 1) (by norm_num)) htest hx

end GlobalPhi43.MW20
