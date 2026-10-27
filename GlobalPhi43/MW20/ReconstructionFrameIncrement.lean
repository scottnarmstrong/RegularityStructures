module

public import GlobalPhi43.MW20.ReconstructionLimit

/-! The frame increment is the actual outer integral of the one-step
germ increment. All convolution and subtraction integrals are justified. -/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures

/-- Exact frame increment identity for the actual constructed MW20 kernels. -/
theorem reconstruction_frame_increment (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (hT₁ : T ≤ 1) (n : ℕ)
    (F : ParabolicSpace × ParabolicSpace → ℝ) (hF : Continuous F) (x : ParabolicSpace) :
    reconstructionFrame Φ hΦ T hT F x n - reconstructionFrame Φ hΦ T hT F x (n + 1) =
      ∫ z, ∫ v, ∫ w,
        F (x + z, x + z + v + w) - F (x + z + v, x + z + v + w)
        ∂reconstructionTail Φ hΦ T hT (n + 1)
        ∂dyadicKernelFactor (kernelProfileMeasure Φ) T n
        ∂dyadicKernelMeasure (kernelProfileMeasure Φ) T n := by
  have := kernelProfileMeasure_probability Φ hΦ
  have := reconstructionTail_probability Φ hΦ hT hT₁ n
  have := reconstructionTail_probability Φ hΦ hT hT₁ (n + 1)
  let H : ℕ → ParabolicSpace → ℝ := fun k a =>
    pastSmooth (reconstructionTail Φ hΦ T hT k) (fun y => F (a, y)) a
  have hH : ∀ k, Continuous (H k) := fun k =>
    reconstruction_kernel_diagonal_test_continuous Φ hΦ (reconstructionScale_pos hT k)
      (reconstructionScale_le_one hT₁ k) F hF
  have hs : ∀ᵐ z ∂dyadicKernelFactor (kernelProfileMeasure Φ) T n,
      ‖z‖ ≤ max ((reconstructionScale T (n + 1)) ^ 2) (reconstructionScale T (n + 1)) := by
    filter_upwards [dyadicKernelFactor_ae_parabolic Φ hΦ hT.le n] with z hz
    exact norm_le_of_pdist_zero_le (reconstructionScale_pos hT (n + 1)).le hz.2
  have hsm := compact_measure_pastSmooth_continuous _ _ hs (H (n + 1)) (hH (n + 1))
  have hi₀ := integrable_dyadic_section (kernelProfileMeasure Φ) hT.le
    (kernelProfileMeasure_ae_parabolic Φ hΦ) n (H n) (hH n) x
  have hi₁ := integrable_dyadic_section (kernelProfileMeasure Φ) hT.le
    (kernelProfileMeasure_ae_parabolic Φ hΦ) n _ hsm x
  have hi₂ := integrable_dyadic_section (kernelProfileMeasure Φ) hT.le
    (kernelProfileMeasure_ae_parabolic Φ hΦ) (n + 1) (H (n + 1)) (hH (n + 1)) x
  have hsucc : dyadicKernelMeasure (kernelProfileMeasure Φ) T (n + 1) =
      (dyadicKernelMeasure (kernelProfileMeasure Φ) T n).conv
        (dyadicKernelFactor (kernelProfileMeasure Φ) T n) := by
    simp only [dyadicKernelMeasure, kernelMeasure_succ, Nat.zero_add]
  rw [hsucc] at hi₂
  change pastSmooth _ (H n) x - pastSmooth _ (H (n + 1)) x = _
  rw [hsucc, pastSmooth_conv_of_integrable _ _ _ x hi₂,
    ← pastSmooth_sub_of_integrable _ _ _ x hi₀ hi₁]
  unfold pastSmooth
  apply integral_congr_ae
  filter_upwards [] with z
  exact reconstruction_tail_step Φ hΦ hT hT₁ n F hF (x + z)

/-- A uniform bound on the actual one-step tests gives the frame increment
bound with constant one, since the outer finite kernel is a probability. -/
theorem reconstruction_frame_increment_le (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (hT₁ : T ≤ 1) (n : ℕ)
    (F : ParabolicSpace × ParabolicSpace → ℝ) (hF : Continuous F) (x : ParabolicSpace)
    {B : ℝ} (hb : ∀ᵐ z ∂dyadicKernelMeasure (kernelProfileMeasure Φ) T n,
      |∫ v, ∫ w, F (x + z, x + z + v + w) - F (x + z + v, x + z + v + w)
        ∂reconstructionTail Φ hΦ T hT (n + 1)
        ∂dyadicKernelFactor (kernelProfileMeasure Φ) T n| ≤ B) :
    |reconstructionFrame Φ hΦ T hT F x n - reconstructionFrame Φ hΦ T hT F x (n + 1)| ≤ B := by
  have := kernelProfileMeasure_probability Φ hΦ
  rw [reconstruction_frame_increment Φ hΦ hT hT₁ n F hF x, ← Real.norm_eq_abs]
  have hh := norm_integral_le_of_norm_le_const (μ := dyadicKernelMeasure (kernelProfileMeasure Φ) T n)
    (f := fun z => ∫ v, ∫ w,
      F (x + z, x + z + v + w) - F (x + z + v, x + z + v + w)
      ∂reconstructionTail Φ hΦ T hT (n + 1)
      ∂dyadicKernelFactor (kernelProfileMeasure Φ) T n)
    (C := B) (by simpa only [Real.norm_eq_abs] using hb)
  simpa using hh

end GlobalPhi43.MW20
