module

public import GlobalPhi43.MW20.SourceHeatSmoothing

/-!
# The augmented convolved remainder equation MW20 (4.27)
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures

/-- The original sup bound pays the actual infinite-kernel defect average.
Only source-cylinder samples are used; no derivative norm of e enters. -/
theorem source_smoothed_defect_le (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (e : ParabolicSpace → ℝ) {T R E : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (hTR : T ≤ R) (he : ∀ z ∈ sourceCylinder 0, |e z| ≤ E)
    {x : ParabolicSpace} (hx : x ∈ sourceCylinder R) :
    |pastSmooth (infiniteKernelMeasure Φ hΦ T hT) e x| ≤ E := by
  have := infiniteKernelMeasure_probability Φ hΦ hT hT1
  have hb : ∀ᵐ y ∂infiniteKernelMeasure Φ hΦ T hT, ‖e (x + y)‖ ≤ E := by
    filter_upwards [infiniteKernelMeasure_ae_sourceCylinder Φ hΦ hT hT1 hTR hx] with y hy
    exact he _ (sourceCylinder_antitone (by norm_num) (sub_nonneg.mpr hTR) hy)
  simpa only [pastSmooth, Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const hb

/-- Convolving the actual defect-bearing signed source equation gives precisely (4.27),
including the retained counterterm and the cubic commutator. Heat commutation
and every test-integrability fact are proved from local source regularity. -/
theorem mw20_augmented_row_4_27 (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {v J V W e : ParabolicSpace → ℝ} (hv : SourceCubicRegularity v)
    (hJ : ContinuousOn J sourceClosedCylinder) (hV : ContinuousOn V sourceClosedCylinder)
    (hW : ContinuousOn W sourceClosedCylinder)
    (he : ContinuousOn e sourceClosedCylinder) (C₂ : ℝ)
    (hPDE : ∀ z ∈ sourceCylinder 0,
      sourceHeat v z = -v z ^ 3 - 3 * (v z ^ 2 * J z) - 3 * (v z * V z) -
        W z - 9 * C₂ * (v z + J z) - e z)
    {T R : ℝ} (hT : 0 < T) (hT1 : T ≤ 1) (hTR : T < R)
    {x : ParabolicSpace} (hx : x ∈ sourceCylinder R) :
    let μ := infiniteKernelMeasure Φ hΦ T hT
    sourceHeat (pastSmooth μ v) x =
      -(pastSmooth μ v x) ^ 3 - 3 * pastSmooth μ (fun z => v z ^ 2 * J z) x -
      3 * pastSmooth μ (fun z => v z * V z) x -
      9 * C₂ * (pastSmooth μ v x + pastSmooth μ J x) - pastSmooth μ W x +
      ((pastSmooth μ v x) ^ 3 - pastSmooth μ (fun z => v z ^ 3) x) - pastSmooth μ e x := by
  have := infiniteKernelMeasure_probability Φ hΦ hT hT1
  let μ := infiniteKernelMeasure Φ hΦ T hT
  have hsample : ∀ᵐ y ∂μ, x + y ∈ sourceClosedCylinder := by
    filter_upwards [infiniteKernelMeasure_ae_sourceCylinder Φ hΦ hT hT1 hTR.le hx] with y hy
    exact sourceCylinder_subset_closed (sub_nonneg.mpr hTR.le) hy
  have hi (f : ParabolicSpace → ℝ) (hf : ContinuousOn f sourceClosedCylinder) :
      Integrable (fun y => f (x + y)) μ :=
    integrable_comp_of_ae_mem_compact μ f isCompact_Icc hf
      (fun y => x + y) (continuous_const.add continuous_id) hsample
  have hiv := hi v hv.continuous
  have hiJ := hi J hJ
  have hiW := hi W hW
  have hie := hi e he
  have hi3 := hi (fun z => v z ^ 3) (hv.continuous.pow 3)
  have hi2J := hi (fun z => v z ^ 2 * J z) ((hv.continuous.pow 2).mul hJ)
  have hivV := hi (fun z => v z * V z) (hv.continuous.mul hV)
  have hsource : (∫ y, sourceHeat v (x + y) ∂μ) =
      -(∫ y, v (x + y) ^ 3 ∂μ) - 3 * (∫ y, v (x + y) ^ 2 * J (x + y) ∂μ) -
      3 * (∫ y, v (x + y) * V (x + y) ∂μ) - (∫ y, W (x + y) ∂μ) -
      9 * C₂ * ((∫ y, v (x + y) ∂μ) + ∫ y, J (x + y) ∂μ) - ∫ y, e (x + y) ∂μ := by
    calc
      _ = ∫ y, -v (x + y) ^ 3 - 3 * (v (x + y) ^ 2 * J (x + y)) -
          3 * (v (x + y) * V (x + y)) - W (x + y) -
          (9 * C₂) * (v (x + y) + J (x + y)) - e (x + y) ∂μ := by
        apply integral_congr_ae
        filter_upwards [infiniteKernelMeasure_ae_sourceCylinder Φ hΦ hT hT1 hTR.le hx] with y hy
        exact hPDE _ (sourceCylinder_antitone (by norm_num) (by linarith) hy)
      _ = _ := by
        have ha := integral_sub hi3.neg (hi2J.const_mul 3)
        have hb := integral_sub (hi3.neg.sub (hi2J.const_mul 3)) (hivV.const_mul 3)
        have hc := integral_sub ((hi3.neg.sub (hi2J.const_mul 3)).sub (hivV.const_mul 3)) hiW
        have hd := integral_sub (((hi3.neg.sub (hi2J.const_mul 3)).sub (hivV.const_mul 3)).sub hiW)
          ((hiv.add hiJ).const_mul (9 * C₂))
        have heq := integral_sub ((((hi3.neg.sub (hi2J.const_mul 3)).sub (hivV.const_mul 3)).sub hiW).sub
          ((hiv.add hiJ).const_mul (9 * C₂))) hie
        simp only [Pi.sub_apply, Pi.neg_apply, Pi.add_apply] at ha hb hc hd heq
        rw [heq, hd, hc, hb, ha, integral_neg, integral_const_mul, integral_const_mul,
          integral_const_mul, integral_add hiv hiJ]
  change sourceHeat (pastSmooth μ v) x = _
  rw [sourceHeat_pastSmooth_infiniteKernel Φ hΦ hv hT hT1 hTR hx]
  change (∫ y, sourceHeat v (x + y) ∂μ) = _
  rw [hsource]
  unfold pastSmooth
  ring

end GlobalPhi43.MW20
