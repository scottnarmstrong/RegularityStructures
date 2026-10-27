module

public import GlobalPhi43.MW20.CubicCommutator
public import GlobalPhi43.MW20.CylinderTesting

/-!
# MW20's cubic commutator for the actual smooth kernel
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures

/-- The pointwise analytic estimate behind MW20 (4.30). The input is
the ordinary local Hölder increment bound on the actual testing cylinder,
not a commutator estimate or an assumed smoothing identity. -/
theorem infiniteKernel_cubic_commutator (Φ : ParabolicSpace → ℝ)
    (hΦ : KernelProfile Φ) (v : ParabolicSpace → ℝ)
    {T R α M H : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) (hTR : T ≤ R)
    (hα : 0 ≤ α) (hH : 0 ≤ H) {x : ParabolicSpace}
    (hx : x ∈ sourceCylinder R)
    (hv : AEStronglyMeasurable (fun y => v (x + y)) (infiniteKernelMeasure Φ hΦ T hT))
    (hbound : ∀ z ∈ sourceCylinder (R - T), |v z| ≤ M)
    (hholder : ∀ z ∈ sourceCylinder (R - T), Local.pdist x z ≤ T →
      |v z - v x| ≤ H * Local.pdist x z ^ α) :
    |(∫ y, v (x + y) ∂infiniteKernelMeasure Φ hΦ T hT) ^ 3 -
      ∫ y, v (x + y) ^ 3 ∂infiniteKernelMeasure Φ hΦ T hT| ≤
      6 * M ^ 2 * H * T ^ α := by
  have := infiniteKernelMeasure_probability Φ hΦ hT hT1
  have hgeom := infiniteKernelMeasure_ae_sourceCylinder Φ hΦ hT hT1 hTR hx
  have hb : ∀ᵐ y ∂infiniteKernelMeasure Φ hΦ T hT, |v (x + y)| ≤ M := by
    filter_upwards [hgeom] with y hy
    exact hbound _ hy
  have ho : ∀ᵐ y ∂infiniteKernelMeasure Φ hΦ T hT,
      |v (x + y) - v x| ≤ H * T ^ α := by
    filter_upwards [hgeom, infiniteKernelMeasure_ae_closedPast Φ hΦ hT hT1] with y hy hys
    have hd : Local.pdist x (x + y) ≤ T := by
      simpa only [Local.pdist_add_right] using hys.2
    exact (hholder _ hy hd).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Local.pdist_nonneg x _) hd hα) hH)
  have hc := probability_cubic_commutator (infiniteKernelMeasure Φ hΦ T hT)
    (fun y => v (x + y)) hv hb ho
  simpa only [mul_assoc] using hc

end GlobalPhi43.MW20
