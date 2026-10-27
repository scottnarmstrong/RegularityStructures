module

public import GlobalPhi43.MW20.AttachmentKernelScaling
public import GlobalPhi43.MW20.KernelPastSupport
public import GlobalPhi43.MW20.InfinitePastSmoothing
public import GlobalPhi43.Attachment.FourDerivativeNorm

/-! The fixed actual MW20 unit profile used by the model-test attachment. -/

public section

namespace GlobalPhi43.Attachment

open MeasureTheory RegularityStructures MW20 Set
open scoped ContDiff

/-- Ψ_1 is the already constructed infinite density at unit scale. -/
@[expose] noncomputable def psiProfile (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) :
    ParabolicSpace → ℝ := infiniteKernel Φ hΦ 1 (by norm_num)

theorem psiProfile_contDiff (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) :
    ContDiff ℝ ∞ (psiProfile Φ hΦ) :=
  infiniteKernel_contDiff Φ hΦ (by norm_num) le_rfl

theorem psiProfile_hasCompactSupport (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) :
    HasCompactSupport (psiProfile Φ hΦ) :=
  infiniteKernel_hasCompactSupport Φ hΦ (by norm_num) le_rfl

/-- Closed support, rather than merely almost-everywhere support, for the C4 test class. -/
theorem psiProfile_tsupport (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) :
    tsupport (psiProfile Φ hΦ) ⊆ {z | z.1 ≤ 0 ∧ Local.pdist 0 z ≤ 1} := by
  have hp : Continuous (fun z : ParabolicSpace => Local.pdist 0 z) := by
    unfold Local.pdist
    fun_prop
  apply closure_minimal _
    ((isClosed_le continuous_fst continuous_const).inter (isClosed_le hp continuous_const))
  intro z hz
  exact infiniteKernel_closedPast_support Φ hΦ (by norm_num) le_rfl hz

/-- The literal Ψ_T(y−x) equals the model conversion's rescaled unit test. -/
theorem infiniteKernel_eq_rescaledTest (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (hT₁ : T ≤ 1) (x y : ParabolicSpace) :
    infiniteKernel Φ hΦ T hT (y-x) = rescaledTestFunction (psiProfile Φ hΦ) T x y := by
  exact infiniteKernel_eq_rescaled_unit Φ hΦ hT hT₁ (y-x)

/-- The reflected smoothing operator is exactly the fixed-profile model test.
Translation changes only the integration variable, without reversing time. -/
theorem infinitePastSmooth_eq_profile_test (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (hT₁ : T ≤ 1) (f : ParabolicSpace → ℝ) (x : ParabolicSpace) :
    infinitePastSmooth Φ hΦ T hT f x =
      ∫ y, f y * rescaledTestFunction (psiProfile Φ hΦ) T x y := by
  have : Measure.IsAddHaarMeasure (volume : Measure ParabolicSpace) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  calc
    infinitePastSmooth Φ hΦ T hT f x =
        ∫ y, infiniteKernel Φ hΦ T hT (y-x) * f y := by
      simpa only [infinitePastSmooth, add_sub_cancel_right, add_sub_cancel_left, add_comm] using
        (integral_add_right_eq_self (μ := volume)
          (fun y => infiniteKernel Φ hΦ T hT (y-x)*f y) x)
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => by
        dsimp only
        rw [infiniteKernel_eq_rescaledTest Φ hΦ hT hT₁]
        exact mul_comm _ _)

end GlobalPhi43.Attachment
