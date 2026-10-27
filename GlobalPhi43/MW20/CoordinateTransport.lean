module

public import GlobalPhi43.MW20.RecenteredTreeScaling
public import GlobalPhi43.MW20.CoordinateSeminorm
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Local Set
open scoped ENNReal

/-- Continuous vector fields are integrable against the actual compact kernel
at every positive scale. No source norm or test bound is assumed. -/
theorem kernel_vector_integrable_all (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0<T) (F : ParabolicSpace → Fin 3 → ℝ) (hF : Continuous F) :
    Integrable F (infiniteKernelMeasure Φ hΦ T hT) := by
  unfold infiniteKernelMeasure
  apply (integrable_withDensity_iff_integrable_smul'
    (ENNReal.measurable_ofReal.comp (infiniteKernel Φ hΦ T hT).continuous.measurable)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)).mpr
  have hc : Continuous (fun z => infiniteKernel Φ hΦ T hT z • F z) :=
    (infiniteKernel Φ hΦ T hT).continuous.smul hF
  have hs := (infiniteKernel_hasCompactSupport_all Φ hΦ hT).smul_right (f' := F)
  simpa only [Function.comp_apply,ENNReal.toReal_ofReal (infiniteKernel_nonneg_all Φ hΦ hT _)] using
    hc.integrable_of_hasCompactSupport (μ := volume) hs

/-- Literal component identity for the original vector test at arbitrary scales. -/
theorem coordinateTreeTest_component_all (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (V : ParabolicSpace → ℝ) (hV : Continuous V) {T : ℝ} (hT : 0<T)
    (x : ParabolicSpace) (i : Fin 3) :
    coordinateTreeTest (mw20TestingKernel Φ hΦ) V T x i =
      infinitePastSmooth Φ hΦ T hT (fun y => (y.2 i-x.2 i)*V y) x := by
  have hi : Integrable (fun w => V (x+w) • w.2) (mw20TestingKernel Φ hΦ T) := by
    rw [mw20TestingKernel_pos Φ hΦ hT]
    exact kernel_vector_integrable_all Φ hΦ hT _ (by fun_prop)
  unfold coordinateTreeTest
  change (ContinuousLinearMap.proj i : (Fin 3 → ℝ) →L[ℝ] ℝ)
    (∫ w, V (x+w) • w.2 ∂mw20TestingKernel Φ hΦ T) = _
  rw [← (ContinuousLinearMap.proj i : (Fin 3 → ℝ) →L[ℝ] ℝ).integral_comp_comm hi,
    ← pastSmooth_infinite_eq_density_all Φ hΦ hT]
  unfold pastSmooth
  rw [mw20TestingKernel_pos Φ hΦ hT]
  apply integral_congr_ae
  filter_upwards [] with w
  simp only [ContinuousLinearMap.proj_apply,Pi.smul_apply,smul_eq_mul,
    Prod.snd_add,Pi.add_apply,add_sub_cancel_left]
  ring

/-- XV has amplitude one: the coordinate increment supplies the inverse length. -/
theorem coordinateTreeTest_parabolicPullback (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (V : ParabolicSpace → ℝ) (hV : Continuous V) (b : ParabolicSpace)
    {ℓ T : ℝ} (hℓ : 0<ℓ) (hT : 0<T) (x : ParabolicSpace) :
    coordinateTreeTest (mw20TestingKernel Φ hΦ) (parabolicPullback (ℓ^2) V b ℓ) T x =
      ℓ • coordinateTreeTest (mw20TestingKernel Φ hΦ) V (ℓ*T) (parabolicMap b ℓ x) := by
  have hm : Continuous (parabolicMap b ℓ) := (parabolicTransport b ℓ hℓ.ne').continuous
  have hvhat : Continuous (parabolicPullback (ℓ^2) V b ℓ) := by
    unfold parabolicPullback
    exact continuous_const.mul (hV.comp hm)
  funext i
  change _ = ℓ*coordinateTreeTest (mw20TestingKernel Φ hΦ) V (ℓ*T) (parabolicMap b ℓ x) i
  rw [coordinateTreeTest_component_all Φ hΦ _ hvhat hT,
    coordinateTreeTest_component_all Φ hΦ V hV (mul_pos hℓ hT)]
  have he : (fun y : ParabolicSpace => (y.2 i-x.2 i)*parabolicPullback (ℓ^2) V b ℓ y) =
      parabolicPullback ℓ (fun y => (y.2 i-(parabolicMap b ℓ x).2 i)*V y) b ℓ := by
    funext y
    simp only [parabolicPullback,parabolicMap,parabolicDilate,Prod.snd_add,
      Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  rw [he,infinitePastSmooth_parabolicPullback Φ hΦ ℓ _ b hℓ hT]

end GlobalPhi43.MW20
