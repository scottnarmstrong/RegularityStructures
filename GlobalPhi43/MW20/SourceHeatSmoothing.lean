module

public import GlobalPhi43.MW20.LocalHeatAverage
public import GlobalPhi43.MW20.LocalAverageRegularity
public import GlobalPhi43.MW20.CompactKernelTube
public import GlobalPhi43.MW20.FiniteSmoothing

/-!
# Heat commutation for the actual infinite MW20 kernel on source cylinders
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures

/-- The actual heat operator commutes with the actual kernel average at
strictly interior source tests. Local C² regularity suffices, with no
regularity or integrability premise outside the source cylinder. -/
theorem sourceHeat_pastSmooth_infiniteKernel (Φ : ParabolicSpace → ℝ)
    (hΦ : KernelProfile Φ) {v : ParabolicSpace → ℝ} (hv : SourceCubicRegularity v)
    {T R : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) (hTR : T < R)
    {x : ParabolicSpace} (hx : x ∈ sourceCylinder R) :
    sourceHeat (pastSmooth (infiniteKernelMeasure Φ hΦ T hT) v) x =
      pastSmooth (infiniteKernelMeasure Φ hΦ T hT) (sourceHeat v) x := by
  have := infiniteKernelMeasure_probability Φ hΦ hT hT1
  obtain ⟨r, δ, hr, hδ, htest⟩ := exists_compact_kernel_testing_tube Φ hΦ hT hT1 hTR hx
  exact sourceHeat_local_average _ v isCompact_Icc Metric.isOpen_ball
    (fun _ hz => hv.contDiffAt_closedInset hr hz) htest (Metric.mem_ball_self hδ)

/-- The actual smoothed source field is C² at every strictly interior test.
This regularity conclusion is derived from local source germs. -/
theorem pastSmooth_infiniteKernel_contDiffAt_two (Φ : ParabolicSpace → ℝ)
    (hΦ : KernelProfile Φ) {v : ParabolicSpace → ℝ} (hv : SourceCubicRegularity v)
    {T R : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) (hTR : T < R)
    {x : ParabolicSpace} (hx : x ∈ sourceCylinder R) :
    ContDiffAt ℝ 2 (pastSmooth (infiniteKernelMeasure Φ hΦ T hT) v) x := by
  have := infiniteKernelMeasure_probability Φ hΦ hT hT1
  obtain ⟨r, δ, hr, hδ, htest⟩ := exists_compact_kernel_testing_tube Φ hΦ hT hT1 hTR hx
  exact contDiffAt_average_on_open_two _ v isCompact_Icc Metric.isOpen_ball
    (fun _ hz => hv.contDiffAt_closedInset hr hz) htest (Metric.mem_ball_self hδ)

end GlobalPhi43.MW20
