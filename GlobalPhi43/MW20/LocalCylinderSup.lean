module

public import GlobalPhi43.MW20.CylinderTesting

/-!
# Cylinder supremum and testing measurability from local regularity
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Set

/-- Local continuity on the closed source cylinder is enough to bound every
interior supremum; no regularity outside that cylinder is imposed. -/
theorem sourceSup_bddAbove_of_continuousOn {v : ParabolicSpace → ℝ}
    (hv : ContinuousOn v sourceClosedCylinder) {R : ℝ} (hR : 0 ≤ R) :
    BddAbove ((fun z => |v z|) '' sourceCylinder R) := by
  have hb : BddAbove ((fun z => |v z|) '' sourceClosedCylinder) :=
    (isCompact_Icc.image_of_continuousOn hv.abs).bddAbove
  exact hb.mono (image_mono (sourceCylinder_subset_closed hR))

/-- The actual supremum controls every source-cylinder value under local
continuity only. -/
theorem abs_le_sourceSup_of_continuousOn {v : ParabolicSpace → ℝ}
    (hv : ContinuousOn v sourceClosedCylinder) {R : ℝ} (hR : 0 ≤ R)
    {z : ParabolicSpace} (hz : z ∈ sourceCylinder R) : |v z| ≤ sourceSup v R :=
  le_csSup (sourceSup_bddAbove_of_continuousOn hv hR) ⟨z, hz, rfl⟩

/-- Local source continuity supplies measurability for the actual kernel
test, using its exact closed-past support and cylinder containment. -/
theorem sourceCylinder_test_aestronglyMeasurable (Φ : ParabolicSpace → ℝ)
    (hΦ : KernelProfile Φ) {v : ParabolicSpace → ℝ}
    (hv : ContinuousOn v sourceClosedCylinder) {T R : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1) (hTR : T ≤ R)
    {x : ParabolicSpace} (hx : x ∈ sourceCylinder R) :
    AEStronglyMeasurable (fun y => v (x + y)) (infiniteKernelMeasure Φ hΦ T hT) := by
  let S : Set ParabolicSpace := {y | x + y ∈ sourceClosedCylinder}
  have hS : MeasurableSet S :=
    (isClosed_Icc.preimage (continuous_const.add continuous_id)).measurableSet
  have hs : ∀ᵐ y ∂infiniteKernelMeasure Φ hΦ T hT, y ∈ S := by
    filter_upwards [infiniteKernelMeasure_ae_sourceCylinder Φ hΦ hT hT1 hTR hx] with y hy
    exact sourceCylinder_subset_closed (sub_nonneg.mpr hTR) hy
  have hc : ContinuousOn (fun y => v (x + y)) S :=
    hv.comp (continuous_const.add continuous_id).continuousOn (fun _ hy => hy)
  have hm := hc.aestronglyMeasurable (μ := infiniteKernelMeasure Φ hΦ T hT) hS
  rwa [Measure.restrict_eq_self_of_ae_mem hs] at hm

end GlobalPhi43.MW20
