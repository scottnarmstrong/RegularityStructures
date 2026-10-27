module

public import GlobalPhi43.MW20.LocalCylinderSup
public import GlobalPhi43.MW20.KernelCubicCommutator

/-!
# Cylinder cubic estimates from MW20 (4.5) and (4.30)
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures


/-- The pointwise form of MW20 (4.30), with its amplitude equal to the actual
source supremum. The Hölder input is its usual pointwise budget on the
larger source cylinder, not an assumed commutator bound. -/
theorem source_cubic_commutator (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {v : ParabolicSpace → ℝ} (hv : ContinuousOn v sourceClosedCylinder)
    {T R α H : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) (hTR : T ≤ R)
    (hα : 0 ≤ α) (hH : 0 ≤ H) {x : ParabolicSpace}
    (hx : x ∈ sourceCylinder R)
    (hholder : ∀ z ∈ sourceCylinder (R - T), Local.pdist x z ≤ T →
      |v z - v x| ≤ H * Local.pdist x z ^ α) :
    |(∫ y, v (x + y) ∂infiniteKernelMeasure Φ hΦ T hT) ^ 3 -
      ∫ y, v (x + y) ^ 3 ∂infiniteKernelMeasure Φ hΦ T hT| ≤
      6 * (sourceSup v (R - T)) ^ 2 * H * T ^ α := by
  exact infiniteKernel_cubic_commutator Φ hΦ v hT hT1 hTR hα hH hx
    (sourceCylinder_test_aestronglyMeasurable Φ hΦ hv hT hT1 hTR hx)
    (fun _ hz => abs_le_sourceSup_of_continuousOn hv (sub_nonneg.mpr hTR) hz) hholder

end GlobalPhi43.MW20
