module

public import GlobalPhi43.MW20.ReconstructionKernelTests
public import GlobalPhi43.MW20.ReconstructionScales

/-! The literal one-step reconstruction identity. All integrability comes
from continuous source sections and compactly concentrated measures. -/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures

/-- Subtract the tested diagonal after one genuine convolution step.
The right side is the precise double germ increment in MW20 section 5.2.1. -/
theorem compact_reconstruction_step
    (σ ν : Measure ParabolicSpace) [IsProbabilityMeasure σ] [IsProbabilityMeasure ν]
    (qσ qν qκ : ℝ) (hσ : ∀ᵐ z ∂σ, ‖z‖ ≤ qσ) (hν : ∀ᵐ w ∂ν, ‖w‖ ≤ qν)
    (hκ : ∀ᵐ v ∂σ.conv ν, ‖v‖ ≤ qκ)
    (F : ParabolicSpace × ParabolicSpace → ℝ) (hF : Continuous F) (a : ParabolicSpace) :
    pastSmooth (σ.conv ν) (fun y => F (a, y)) a -
      pastSmooth σ (fun b => pastSmooth ν (fun y => F (b, y)) b) a =
      ∫ z, ∫ w, F (a, a + z + w) - F (a + z, a + z + w) ∂ν ∂σ := by
  have hFa : Continuous (fun y => F (a, y)) :=
    hF.comp (continuous_const.prodMk continuous_id)
  have hi := compact_past_section_integrable (σ.conv ν) qκ hκ _ hFa a
  rw [pastSmooth_conv_of_integrable σ ν _ a hi]
  have hfirst := compact_measure_pastSmooth_continuous ν qν hν _ hFa
  have hsecond := compact_measure_diagonal_test_continuous ν qν hν F hF
  have hi₁ := compact_past_section_integrable σ qσ hσ _ hfirst a
  have hi₂ := compact_past_section_integrable σ qσ hσ _ hsecond a
  rw [← pastSmooth_sub_of_integrable σ _ _ a hi₁ hi₂]
  unfold pastSmooth
  apply integral_congr_ae
  filter_upwards [] with z
  have hiw₁ := compact_past_section_integrable ν qν hν _ hFa (a + z)
  have hiw₂ := compact_past_section_integrable ν qν hν (fun y => F (a + z, y))
    (hF.comp (continuous_const.prodMk continuous_id)) (a + z)
  exact (integral_sub hiw₁ hiw₂).symm

/-- The preceding identity instantiated with the actual infinite kernel tails
and the actual dyadic factor; no factorisation premise is supplied by a caller. -/
theorem reconstruction_tail_step (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (hT₁ : T ≤ 1) (n : ℕ)
    (F : ParabolicSpace × ParabolicSpace → ℝ) (hF : Continuous F) (a : ParabolicSpace) :
    pastSmooth (reconstructionTail Φ hΦ T hT n) (fun y => F (a, y)) a -
      pastSmooth (dyadicKernelFactor (kernelProfileMeasure Φ) T n)
        (fun b => pastSmooth (reconstructionTail Φ hΦ T hT (n + 1))
          (fun y => F (b, y)) b) a =
      ∫ z, ∫ w, F (a, a + z + w) - F (a + z, a + z + w)
        ∂reconstructionTail Φ hΦ T hT (n + 1)
        ∂dyadicKernelFactor (kernelProfileMeasure Φ) T n := by
  have := kernelProfileMeasure_probability Φ hΦ
  have := reconstructionTail_probability Φ hΦ hT hT₁ (n + 1)
  have hs : ∀ᵐ z ∂dyadicKernelFactor (kernelProfileMeasure Φ) T n,
      ‖z‖ ≤ max ((reconstructionScale T (n + 1)) ^ 2) (reconstructionScale T (n + 1)) := by
    filter_upwards [dyadicKernelFactor_ae_parabolic Φ hΦ hT.le n] with z hz
    exact norm_le_of_pdist_zero_le (reconstructionScale_pos hT (n + 1)).le hz.2
  have hn := reconstruction_kernel_norm_support Φ hΦ (reconstructionScale_pos hT (n + 1))
    (reconstructionScale_le_one hT₁ (n + 1))
  have hk := reconstruction_kernel_norm_support Φ hΦ (reconstructionScale_pos hT n)
    (reconstructionScale_le_one hT₁ n)
  change ∀ᵐ w ∂reconstructionTail Φ hΦ T hT n,
    ‖w‖ ≤ max ((reconstructionScale T n) ^ 2) (reconstructionScale T n) at hk
  rw [reconstructionTail_recursion Φ hΦ hT hT₁ n] at hk ⊢
  exact compact_reconstruction_step (dyadicKernelFactor (kernelProfileMeasure Φ) T n)
    (reconstructionTail Φ hΦ T hT (n + 1)) _ _ _ hs hn hk F hF a

end GlobalPhi43.MW20
