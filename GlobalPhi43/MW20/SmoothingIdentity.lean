module

public import GlobalPhi43.MW20.KernelSequenceLimit
public import GlobalPhi43.MW20.KernelNegativeSeminorms
public import GlobalPhi43.MW20.Setting.MWSmooth

/-! The kernel smoothing integral equals past smoothing, with y-x orientation. -/

public section
namespace GlobalPhi43.MW20
open MeasureTheory RegularityStructures

/-- The density/measure change of variables also applies to the XV vector integral.
No measurability or integrability certificate is assumed for this total-integral identity. -/
theorem integral_mwKernel_smul_eq_integral_infiniteKernelMeasure {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0<T) (hT1 : T≤1) (f : ParabolicSpace → E) (x : ParabolicSpace) :
    (∫ y, mwKernel Φ T (y-x) • f y) =
      ∫ w, f (x+w) ∂infiniteKernelMeasure Φ hΦ T hT := by
  have : Measure.IsAddHaarMeasure (volume : Measure ParabolicSpace) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  simp_rw [mwKernel_eq_infiniteKernel Φ hΦ hT hT1]
  rw [infiniteKernelMeasure,integral_withDensity_eq_integral_toReal_smul
    (f := fun z => ENNReal.ofReal (infiniteKernel Φ hΦ T hT z))
    (ENNReal.measurable_ofReal.comp (infiniteKernel Φ hΦ T hT).continuous.measurable)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (infiniteKernel_nonneg Φ hΦ hT hT1 _)]
  rw [← integral_add_left_eq_self (fun y => infiniteKernel Φ hΦ T hT (y-x) • f y) x]
  simp only [add_sub_cancel_left]

theorem mwSmooth_eq_pastSmooth (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0<T) (hT1 : T≤1) (f : ParabolicSpace → ℝ) (x : ParabolicSpace) :
    mwSmooth Φ T f x = pastSmooth (mw20TestingKernel Φ hΦ T) f x := by
  rw [mw20TestingKernel_pos Φ hΦ hT]
  exact integral_mwKernel_smul_eq_integral_infiniteKernelMeasure Φ hΦ hT hT1 f x

end GlobalPhi43.MW20
