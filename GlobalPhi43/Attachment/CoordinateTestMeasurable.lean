module

public import GlobalPhi43.Attachment.GermSeminormMeasurable
public import GlobalPhi43.MW20.KernelCoordinateSeminorm

/-! The vector coordinate test as three actual unit-kernel integrals. -/

@[expose] public noncomputable section

namespace GlobalPhi43.Attachment
open MeasureTheory RegularityStructures MW20 Set

/-- Unit-scale coordinates retain the source vector norm. -/
def unitCoordinateTest (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (V : ParabolicSpace → ℝ) (p : ParabolicSpace × ℝ) : Fin 3 → ℝ :=
  fun i => unitGermAverage Φ hΦ (fun q => (q.2.2 i - q.1.2 i) * V q.2) p

/-- Exact normalization of the actual vector integral, without a supplied integrability hypothesis. -/
theorem coordinateTreeTest_eq_unit (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (V : ParabolicSpace → ℝ) (hV : Continuous V) (x : ParabolicSpace)
    {t : ℝ} (ht : 0 < t) (ht₁ : t ≤ 1) :
    coordinateTreeTest (mw20TestingKernel Φ hΦ) V t x = unitCoordinateTest Φ hΦ V (x, t) := by
  ext i
  have hi := mw20_coordinateTree_integrable Φ hΦ V hV x ht ht₁
  have he : pastSmooth (mw20TestingKernel Φ hΦ t) (fun y => (y.2 i - x.2 i) * V y) x =
      coordinateTreeTest (mw20TestingKernel Φ hΦ) V t x i := by
    unfold pastSmooth coordinateTreeTest
    change (∫ z, ((x + z).2 i - x.2 i) * V (x + z) ∂mw20TestingKernel Φ hΦ t) =
      (ContinuousLinearMap.proj i : (Fin 3 → ℝ) →L[ℝ] ℝ)
        (∫ z, V (x + z) • z.2 ∂mw20TestingKernel Φ hΦ t)
    rw [← (ContinuousLinearMap.proj i : (Fin 3 → ℝ) →L[ℝ] ℝ).integral_comp_comm hi]
    apply integral_congr_ae
    filter_upwards with z
    simp only [ContinuousLinearMap.proj_apply, Pi.smul_apply, smul_eq_mul,
      Prod.snd_add, Pi.add_apply, add_sub_cancel_left]
    ring
  rw [← he]
  exact pastSmooth_eq_unitGermAverage Φ hΦ ht ht₁
    (G := fun q => (q.2.2 i - q.1.2 i) * V q.2) (x := x)

/-- Joint continuity includes base point and scale. -/
theorem unitCoordinateTest_continuous (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (V : ParabolicSpace → ℝ) (hV : Continuous V) : Continuous (unitCoordinateTest Φ hΦ V) := by
  apply continuous_pi
  intro i
  apply unitGermAverage_continuous
  exact ((continuous_apply i |>.comp continuous_snd |>.comp continuous_snd).sub
    (continuous_apply i |>.comp continuous_snd |>.comp continuous_fst)).mul (hV.comp continuous_snd)

/-- Fixed-point measurability holds for the full vector integral. -/
theorem unitCoordinateTest_measurable {Ω : Type*} [MeasurableSpace Ω]
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) (V : Ω → ParabolicSpace → ℝ)
    (hc : ∀ ω, Continuous (V ω)) (hm : ∀ x, Measurable (fun ω => V ω x))
    (p : ParabolicSpace × ℝ) : Measurable (fun ω => unitCoordinateTest Φ hΦ (V ω) p) := by
  apply measurable_pi_iff.mpr
  intro i
  apply unitGermAverage_measurable Φ hΦ
    (fun ω q => (q.2.2 i - q.1.2 i) * V ω q.2)
  · intro ω
    exact ((continuous_apply i |>.comp continuous_snd |>.comp continuous_snd).sub
      (continuous_apply i |>.comp continuous_snd |>.comp continuous_fst)).mul ((hc ω).comp continuous_snd)
  · intro q
    exact measurable_const.mul (hm q.2)

end GlobalPhi43.Attachment
