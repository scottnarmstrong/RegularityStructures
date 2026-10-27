module

public import GlobalPhi43.Invariant.KrylovBogoliubov

/-! # Full and late averages have the same weak limit -/

public noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace GlobalPhi43.Invariant

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]

/-- Deleting the first time unit changes each bounded test by at most 2 norm(f)/T. -/
theorem abs_fullAverage_sub_lateAverage_le (ρ : Kernel ℝ E) [IsMarkovKernel ρ]
    {T : ℝ} (hT : 1 < T) (f : E →ᵇ ℝ) :
    |(∫ y, f y ∂fullAverage ρ T) - ∫ y, f y ∂lateAverage ρ T| ≤
      2 * ‖f‖ / T := by
  let g : ℝ → ℝ := fun t => ∫ y, f y ∂ρ t
  have hg : Measurable g := f.continuous.measurable.stronglyMeasurable.integral_kernel.measurable
  have hb (t : ℝ) : ‖g t‖ ≤ ‖f‖ := by
    simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := ρ t)
        (ae_of_all _ fun y => f.norm_coe_le_norm y))
  have hi := intervalIntegrable_of_measurable_bounded hg hb
  have h0T : 0 < T := lt_trans zero_lt_one hT
  have hTm : 0 < T - 1 := sub_pos.mpr hT
  rw [fullAverage, lateAverage,
    integral_intervalAverage _ _ _ f.continuous.measurable ‖f‖
      (fun y => f.norm_coe_le_norm y),
    integral_intervalAverage _ _ _ f.continuous.measurable ‖f‖
      (fun y => f.norm_coe_le_norm y), sub_zero,
    ← intervalIntegral.integral_of_le h0T.le,
    ← intervalIntegral.integral_of_le hT.le]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hi 0 1) (hi 1 T)
  change |T⁻¹ * (∫ t in 0..T, g t) - (T - 1)⁻¹ * (∫ t in 1..T, g t)| ≤ _
  rw [← hsplit]
  have halg (A B : ℝ) : T⁻¹ * (A + B) - (T - 1)⁻¹ * B =
      T⁻¹ * A - (T⁻¹ * (T - 1)⁻¹) * B := by
    field_simp
    ring
  rw [halg]
  have h1 := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (fun t _ => hb t)
  have h2 := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (1 : ℝ)) (b := T) (fun t _ => hb t)
  simp only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] at h1
  rw [abs_of_pos hTm] at h2
  have hcoef : 0 ≤ T⁻¹ * (T - 1)⁻¹ := mul_nonneg (inv_nonneg.mpr h0T.le)
    (inv_nonneg.mpr hTm.le)
  calc
    _ ≤ |T⁻¹ * (∫ t in 0..1, g t)| +
        |(T⁻¹ * (T - 1)⁻¹) * (∫ t in 1..T, g t)| := abs_sub _ _
    _ = T⁻¹ * |∫ t in 0..1, g t| +
        (T⁻¹ * (T - 1)⁻¹) * |∫ t in 1..T, g t| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (inv_nonneg.mpr h0T.le), abs_of_nonneg hcoef]
    _ ≤ T⁻¹ * ‖f‖ + (T⁻¹ * (T - 1)⁻¹) * (‖f‖ * (T - 1)) :=
      add_le_add (mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr h0T.le))
        (mul_le_mul_of_nonneg_left h2 hcoef)
    _ = 2 * ‖f‖ / T := by
      field_simp
      ring

/-- The full/late discrepancy tends to zero along every sequence of diverging times. -/
theorem full_late_test_difference_tendsto_zero (ρ : Kernel ℝ E) [IsMarkovKernel ρ]
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) (f : E →ᵇ ℝ) :
    Tendsto (fun n => (∫ y, f y ∂fullAverage ρ (T n)) -
      ∫ y, f y ∂lateAverage ρ (T n)) atTop (𝓝 0) := by
  have hb : ∀ᶠ n in atTop,
      ‖(∫ y, f y ∂fullAverage ρ (T n)) - ∫ y, f y ∂lateAverage ρ (T n)‖ ≤
        2 * ‖f‖ / T n := by
    filter_upwards [hT.eventually_gt_atTop 1] with n hn
    exact abs_fullAverage_sub_lateAverage_le ρ hn f
  apply squeeze_zero_norm' hb
  have h := (tendsto_const_nhds (x := 2 * ‖f‖)).mul (tendsto_inv_atTop_zero.comp hT)
  simpa only [Function.comp_apply, div_eq_mul_inv, mul_zero] using h

/-- Full averages have the same supplied weak probability limit as late averages. -/
theorem tendsto_fullAverage_of_lateAverage (ρ : Kernel ℝ E) [IsMarkovKernel ρ]
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop)
    {full late : ℕ → ProbabilityMeasure E}
    (hfull : ∀ n, (full n : Measure E) = fullAverage ρ (T n))
    (hlate : ∀ n, (late n : Measure E) = lateAverage ρ (T n))
    {μ : ProbabilityMeasure E} (hμ : Tendsto late atTop (𝓝 μ)) :
    Tendsto full atTop (𝓝 μ) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have hd := full_late_test_difference_tendsto_zero ρ hT f
  have hl := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ f
  simp_rw [hlate] at hl
  have he := hd.add hl
  simp only [sub_add_cancel, zero_add] at he
  simpa only [hfull] using he

end GlobalPhi43.Invariant
