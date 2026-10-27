module

public import GlobalPhi43.MW20.PastBallTesting
public import GlobalPhi43.MW20.FiniteSmoothing
public import GlobalPhi43.MW20.LocalSourcePairNorms

/-!
# The cubic row (4.5) on literal small-scale mixed-domain testing balls
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures

/-- Testing-ball form of (4.5), with amplitude on the original parent P_r. -/
theorem source_smoothed_cube_testing_ball (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {v : ParabolicSpace → ℝ} (hv : ContinuousOn v sourceClosedCylinder)
    {T L r d : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) (hr : 0 ≤ r) (hd : 0 ≤ d)
    {x y : ParabolicSpace} (hball : Local.pastBall x (L + T) ⊆ Local.cylinderInterior r d)
    (hy : y ∈ Local.pastBall x L) :
    |pastSmooth (infiniteKernelMeasure Φ hΦ T hT) (fun z => v z ^ 3) y| ≤ sourceSup v r ^ 3 := by
  have := infiniteKernelMeasure_probability Φ hΦ hT hT1
  have hb : ∀ᵐ z ∂infiniteKernelMeasure Φ hΦ T hT, ‖v (y + z) ^ 3‖ ≤ sourceSup v r ^ 3 := by
    filter_upwards [infiniteKernelMeasure_ae_testingDomain Φ hΦ hT hT1 hball hy] with z hz
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _)
      (abs_le_sourceSup_of_continuousOn hv hr (mixedInterior_subset_base hd hz)) 3
  simpa only [pastSmooth, Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const hb

end GlobalPhi43.MW20
