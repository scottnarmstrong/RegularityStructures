module

public import GlobalPhi43.MW20.CompactTestIntegral
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Differentiating averages using only regularity on the tested compact set
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory Filter Topology Set
open scoped ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Differentiation of an actual finite-measure average from C¹ germs on its
compact testing neighbourhood. The field is unrestricted outside that set. -/
theorem hasFDerivAt_local_average (μ : Measure E) [IsFiniteMeasure μ]
    (f : E → F) {K : Set E} (hK : IsCompact K)
    (hf : ∀ w ∈ K, ContDiffAt ℝ 1 f w)
    (x : E) {δ : ℝ} (hδ : 0 < δ)
    (htest : ∀ᵐ y ∂μ, ∀ z ∈ Metric.ball x δ, z + y ∈ K) :
    HasFDerivAt (fun z => ∫ y, f (z + y) ∂μ)
      (∫ y, fderiv ℝ f (x + y) ∂μ) x := by
  have hcf : ContinuousOn f K := fun w hw => (hf w hw).continuousAt.continuousWithinAt
  have hcd : ContinuousOn (fderiv ℝ f) K := fun w hw =>
    ((hf w hw).continuousAt_fderiv one_ne_zero).continuousWithinAt
  have hx : x ∈ Metric.ball x δ := Metric.mem_ball_self hδ
  have hmem : ∀ z ∈ Metric.ball x δ, ∀ᵐ y ∂μ, z + y ∈ K := by
    intro z hz
    filter_upwards [htest] with y hy
    exact hy z hz
  obtain ⟨B, hB⟩ := (hK.image_of_continuousOn hcd.norm).bddAbove
  have hi (z : E) (hz : z ∈ Metric.ball x δ) : Integrable (fun y => f (z + y)) μ :=
    integrable_comp_of_ae_mem_compact μ f hK hcf (fun y => z + y)
      (continuous_const.add continuous_id) (hmem z hz)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Metric.ball x δ) (F' := fun z y => fderiv ℝ f (z + y))
    (bound := fun _ => |B|) (Metric.ball_mem_nhds x hδ)
  · filter_upwards [Metric.ball_mem_nhds x hδ] with z hz
    exact (hi z hz).aestronglyMeasurable
  · exact hi x hx
  · exact (integrable_comp_of_ae_mem_compact μ (fderiv ℝ f) hK hcd
      (fun y => x + y) (continuous_const.add continuous_id) (hmem x hx)).aestronglyMeasurable
  · filter_upwards [htest] with y hy
    intro z hz
    exact (hB ⟨z + y, hy z hz, rfl⟩).trans (le_abs_self B)
  · exact integrable_const _
  · filter_upwards [htest] with y hy
    intro z hz
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using!
      ((hf _ (hy z hz)).differentiableAt one_ne_zero).hasFDerivAt.comp z
        ((hasFDerivAt_id z).add_const y)

end GlobalPhi43.MW20
