module

public import GlobalPhi43.Attachment.ProbeFoldIntegral

/-! Integrability of actual continuous-field compact-test pairings, including
physical dilations and reflection at the original base point. -/

@[expose] public noncomputable section

open RegularityStructures MeasureTheory
open scoped ContDiff

namespace GlobalPhi43.Attachment

def probeScaleHomeomorph (a : ℝ) (ha : a ≠ 0) : ParabolicSpace ≃ₜ ParabolicSpace where
  toFun := parabolicDilate a
  invFun := parabolicDilate a⁻¹
  left_inv := parabolicDilate_inv_parabolicDilate ha
  right_inv := parabolicDilate_parabolicDilate_inv ha
  continuous_toFun := (parabolicDilateCLM a).continuous
  continuous_invFun := (parabolicDilateCLM a⁻¹).continuous

theorem probe_rescaledTest_compact {φ : ParabolicSpace → ℝ} (hc : HasCompactSupport φ)
    {T : ℝ} (hT : 0 < T) (z : ParabolicSpace) :
    HasCompactSupport (rescaledTestFunction φ T z) := by
  have hh := hc.comp_homeomorph
    ((Homeomorph.addRight (-z)).trans (probeScaleHomeomorph T⁻¹ (inv_ne_zero hT.ne')))
  change HasCompactSupport (fun w => (T^5)⁻¹ * φ (parabolicDilate T⁻¹ (w-z)))
  have hhc : HasCompactSupport (fun w => φ (parabolicDilate T⁻¹ (w-z))) := by
    change HasCompactSupport (fun w => φ (parabolicDilate T⁻¹ (w + -z))) at hh
    simpa only [sub_eq_add_neg] using hh
  apply hhc.mono
  intro w hw
  change (T^5)⁻¹ * φ (parabolicDilate T⁻¹ (w-z)) ≠ 0 at hw
  change φ (parabolicDilate T⁻¹ (w-z)) ≠ 0
  intro he
  exact hw (by rw [he, mul_zero])

theorem probe_rescaledTest_continuous {φ : ParabolicSpace → ℝ} (hφ : Continuous φ)
    (T : ℝ) (z : ParabolicSpace) : Continuous (rescaledTestFunction φ T z) := by
  unfold rescaledTestFunction
  have hh : Continuous (fun w : ParabolicSpace =>
      (T^5)⁻¹ * φ (parabolicDilateCLM T⁻¹ (w-z))) := continuous_const.mul (hφ.comp
    ((parabolicDilateCLM T⁻¹).continuous.comp
      (continuous_id.sub continuous_const : Continuous (fun w : ParabolicSpace => w-z))))
  simpa only [parabolicDilateCLM_apply] using hh

theorem probe_test_pairing_integrable {f φ : ParabolicSpace → ℝ} (hf : Continuous f)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) {T : ℝ} (hT : 0 < T)
    (z : ParabolicSpace) :
    Integrable (fun w => f w * rescaledTestFunction φ T z w) :=
  (hf.mul (probe_rescaledTest_continuous hφ T z)).integrable_of_hasCompactSupport
    (probe_rescaledTest_compact hc hT z).mul_left

end GlobalPhi43.Attachment
