module

public import GlobalPhi43.MW20.SourceHeatSmoothing

/-!
# Heat commutation for globally smooth source fields at arbitrary test points
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Set

/-- The actual source kernel has a proved ordinary norm bound on source scales. -/
theorem infiniteKernelMeasure_ae_norm_le (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) :
    ∀ᵐ z ∂infiniteKernelMeasure Φ hΦ T hT, ‖z‖ ≤ T := by
  filter_upwards [infiniteKernelMeasure_ae_closedPast Φ hΦ hT hT1] with z hz
  have hn := (norm_sub_le_pdist (hz.2.trans hT1)).trans hz.2
  simpa only [zero_sub, norm_neg] using hn

/-- Standing global smoothness gives heat commutation at every point.
The compact testing tube is constructed; no cylinder inset or independently
supplied derivative integrability assumption is needed. -/
theorem sourceHeat_pastSmooth_global (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ 2 f)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) (x : ParabolicSpace) :
    sourceHeat (pastSmooth (infiniteKernelMeasure Φ hΦ T hT) f) x =
      pastSmooth (infiniteKernelMeasure Φ hΦ T hT) (sourceHeat f) x := by
  have := infiniteKernelMeasure_probability Φ hΦ hT hT1
  have htest : ∀ᵐ z ∂infiniteKernelMeasure Φ hΦ T hT,
      ∀ w ∈ Metric.ball x 1, w + z ∈ Metric.closedBall x (T + 1) := by
    filter_upwards [infiniteKernelMeasure_ae_norm_le Φ hΦ hT hT1] with z hz
    intro w hw
    apply Metric.mem_closedBall.mpr
    rw [dist_eq_norm]
    have hw' : ‖w - x‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hw
    calc
      ‖w + z - x‖ = ‖(w - x) + z‖ := by congr 1; abel
      _ ≤ ‖w - x‖ + ‖z‖ := norm_add_le _ _
      _ ≤ T + 1 := by linarith
  exact sourceHeat_local_average _ f (isCompact_closedBall x (T + 1)) Metric.isOpen_ball
    (fun _ _ => hf.contDiffAt) htest (by simp only [Metric.mem_ball, dist_self]; norm_num)

end GlobalPhi43.MW20
