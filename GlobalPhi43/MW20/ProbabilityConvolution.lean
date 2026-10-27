module

public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Tactic

/-!
# Probability convolution on bounded continuous fields

The relative variable is subtracted here: this is convolution of kernel
densities, before the reflection used for past-looking ordinary smoothing.
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction NNReal

variable {E F : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ F] in
/-- A translated bounded continuous field is integrable against a finite measure. -/
theorem integrable_bounded_translate (μ : Measure E) [IsFiniteMeasure μ]
    (f : E →ᵇ F) (x : E) : Integrable (fun y => f (x - y)) μ := by
  have hc : Continuous (fun y => f (x - y)) := f.continuous.comp (continuous_const.sub continuous_id)
  exact (integrable_const ‖f‖).mono' hc.stronglyMeasurable.aestronglyMeasurable
    (ae_of_all μ fun y => f.norm_coe_le_norm (x - y))

/-- Continuity of actual probability convolution, by dominated convergence. -/
theorem continuous_probabilityConvolution (μ : Measure E) [IsProbabilityMeasure μ]
    (f : E →ᵇ F) : Continuous (fun x => ∫ y, f (x - y) ∂μ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_integral_filter_of_dominated_convergence (fun _ : E => ‖f‖)
  · exact Eventually.of_forall fun z => (integrable_bounded_translate μ f z).aestronglyMeasurable
  · exact Eventually.of_forall fun z => ae_of_all μ fun y => f.norm_coe_le_norm (z - y)
  · exact integrable_const _
  · exact ae_of_all μ fun y => (f.continuous.comp (continuous_id.sub continuous_const)).continuousAt.tendsto

omit [BorelSpace E] [SecondCountableTopology E] in
/-- The average of translated values stays within the original uniform norm. -/
theorem norm_probabilityConvolution_apply_le (μ : Measure E) [IsProbabilityMeasure μ]
    (f : E →ᵇ F) (x : E) : ‖∫ y, f (x - y) ∂μ‖ ≤ ‖f‖ := by
  simpa using norm_integral_le_of_norm_le_const (ae_of_all μ fun y => f.norm_coe_le_norm (x - y))

/-- Convolution by an actual probability measure, bundled in the uniform norm. -/
@[expose] noncomputable def probabilityConvolution (μ : Measure E) [IsProbabilityMeasure μ]
    (f : E →ᵇ F) : E →ᵇ F :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => ∫ y, f (x - y) ∂μ)
    (continuous_probabilityConvolution μ f) ‖f‖ (norm_probabilityConvolution_apply_le μ f)

@[simp] theorem probabilityConvolution_apply (μ : Measure E) [IsProbabilityMeasure μ]
    (f : E →ᵇ F) (x : E) : probabilityConvolution μ f x = ∫ y, f (x - y) ∂μ := rfl

/-- Probability convolution contracts the uniform norm. -/
theorem norm_probabilityConvolution_le (μ : Measure E) [IsProbabilityMeasure μ]
    (f : E →ᵇ F) : ‖probabilityConvolution μ f‖ ≤ ‖f‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg f)).2 (norm_probabilityConvolution_apply_le μ f)

/-- Probability convolution preserves every global Lipschitz constant. -/
theorem lipschitz_probabilityConvolution (μ : Measure E) [IsProbabilityMeasure μ]
    (f : E →ᵇ F) {K : ℝ≥0} (hf : LipschitzWith K f) :
    LipschitzWith K (probabilityConvolution μ f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  rw [dist_eq_norm, probabilityConvolution_apply, probabilityConvolution_apply,
    ← integral_sub (integrable_bounded_translate μ f x) (integrable_bounded_translate μ f z)]
  have hb : ∀ᵐ y ∂μ, ‖f (x - y) - f (z - y)‖ ≤ (K : ℝ) * dist x z := by
    apply ae_of_all
    intro y
    simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using hf.dist_le_mul (x - y) (z - y)
  simpa using norm_integral_le_of_norm_le_const hb

/-- A probability measure supported at radius r changes a Lipschitz field by
at most K r in uniform norm. This is the summable increment used for Ψ. -/
theorem norm_probabilityConvolution_sub_le [CompleteSpace F] (μ : Measure E) [IsProbabilityMeasure μ]
    (f : E →ᵇ F) {K : ℝ≥0} (hf : LipschitzWith K f) {r : ℝ} (hr : 0 ≤ r)
    (hsupp : ∀ᵐ y ∂μ, ‖y‖ ≤ r) : ‖probabilityConvolution μ f - f‖ ≤ (K : ℝ) * r := by
  apply (BoundedContinuousFunction.norm_le (mul_nonneg K.coe_nonneg hr)).2
  intro x
  change ‖(∫ y, f (x - y) ∂μ) - f x‖ ≤ (K : ℝ) * r
  have heq : (∫ y, f (x - y) - f x ∂μ) = (∫ y, f (x - y) ∂μ) - f x := by
    rw [integral_sub (integrable_bounded_translate μ f x) (integrable_const _)]
    simp
  rw [← heq]
  have hb : ∀ᵐ y ∂μ, ‖f (x - y) - f x‖ ≤ (K : ℝ) * r := by
    filter_upwards [hsupp] with y hy
    have hl := hf.dist_le_mul (x - y) x
    simp only [dist_eq_norm, sub_sub_cancel_left, norm_neg] at hl
    exact hl.trans (mul_le_mul_of_nonneg_left hy K.coe_nonneg)
  simpa using norm_integral_le_of_norm_le_const hb

end GlobalPhi43.MW20
