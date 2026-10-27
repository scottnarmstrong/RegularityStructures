module

public import GlobalPhi43.MW20.InfiniteOuterDiagonal
public import GlobalPhi43.MW20.ReconstructionStep

/-! Identify the reconstruction telescope limit with the actual smoothed
source diagonal, using the proved kernel block identity. -/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Set Filter
open scoped Topology

/-- The actual finite-outer, infinite-inner frame of MW20 section 5.2.1. -/
@[expose] noncomputable def reconstructionFrame (Φ : ParabolicSpace → ℝ)
    (hΦ : KernelProfile Φ) (T : ℝ) (hT : 0 < T)
    (F : ParabolicSpace × ParabolicSpace → ℝ) (x : ParabolicSpace) (n : ℕ) : ℝ :=
  pastSmooth (dyadicKernelMeasure (kernelProfileMeasure Φ) T n)
    (fun a => pastSmooth (reconstructionTail Φ hΦ T hT n) (fun y => F (a, y)) a) x

/-- Frame convergence to the finite smoothed diagonal, with a varying actual
outer kernel. The error tends to zero without any outer weak-limit premise. -/
theorem reconstruction_frame_diagonal_error (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (hT₁ : T ≤ 1)
    (F : ParabolicSpace × ParabolicSpace → ℝ) (hF : Continuous F) (x : ParabolicSpace) :
    Tendsto (fun n => reconstructionFrame Φ hΦ T hT F x n -
      pastSmooth (dyadicKernelMeasure (kernelProfileMeasure Φ) T n) (fun a => F (a, a)) x)
      atTop (𝓝 0) := by
  have := kernelProfileMeasure_probability Φ hΦ
  let G : ParabolicSpace × ParabolicSpace → ℝ := fun p => F (x + p.1, x + p.2)
  have hG : Continuous G := by dsimp [G]; apply hF.comp; fun_prop
  have hu := reconstruction_outer_diagonal_limit Φ hΦ (reconstructionScale T)
    (reconstructionScale_pos hT) (reconstructionScale_le_one hT₁)
    (reconstructionScale_tendsto_zero T) G hG
    (Metric.closedBall 0 (max (T ^ 2) T)) (isCompact_closedBall _ _)
    (dyadicKernelMeasure (kernelProfileMeasure Φ) T) (fun n => by
      simpa only [Metric.mem_closedBall, dist_zero_right] using
        dyadicKernelMeasure_ae_norm_le (kernelProfileMeasure Φ) hT.le
          (kernelProfileMeasure_ae_parabolic Φ hΦ) n)
  simpa only [G, reconstructionFrame, reconstructionTail, pastSmooth, add_assoc] using hu

/-- Every frame for a germ depending only on its second variable equals the
actual infinite-kernel test, by the exact block factorisation. -/
theorem reconstruction_frame_second_variable (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (hT₁ : T ≤ 1)
    (g : ParabolicSpace → ℝ) (hg : Continuous g) (x : ParabolicSpace) (n : ℕ) :
    reconstructionFrame Φ hΦ T hT (fun p => g p.2) x n =
      pastSmooth (infiniteKernelMeasure Φ hΦ T hT) g x := by
  have := kernelProfileMeasure_probability Φ hΦ
  have := reconstructionTail_probability Φ hΦ hT hT₁ n
  have hi := reconstruction_kernel_section_integrable Φ hΦ hT hT₁ g hg x
  rw [reconstructionTail_block Φ hΦ hT hT₁ n] at hi ⊢
  exact (pastSmooth_conv_of_integrable (dyadicKernelMeasure (kernelProfileMeasure Φ) T n)
    (reconstructionTail Φ hΦ T hT n) g x hi).symm

/-- The telescope limit is proved from actual kernels and source continuity.
It is the infinite-kernel smoothing of the source's diagonal. -/
theorem reconstruction_frame_tendsto (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T : ℝ} (hT : 0 < T) (hT₁ : T ≤ 1)
    (F : ParabolicSpace × ParabolicSpace → ℝ) (hF : Continuous F) (x : ParabolicSpace) :
    Tendsto (reconstructionFrame Φ hΦ T hT F x) atTop
      (𝓝 (pastSmooth (infiniteKernelMeasure Φ hΦ T hT) (fun a => F (a, a)) x)) := by
  have hdiag : Continuous (fun a => F (a, a)) := hF.comp (continuous_id.prodMk continuous_id)
  have hG : Continuous (fun p : ParabolicSpace × ParabolicSpace => F (p.2, p.2)) :=
    hdiag.comp continuous_snd
  have h₁ := reconstruction_frame_diagonal_error Φ hΦ hT hT₁ F hF x
  have h₂ := reconstruction_frame_diagonal_error Φ hΦ hT hT₁ _ hG x
  simp only [reconstruction_frame_second_variable Φ hΦ hT hT₁ _ hdiag x] at h₂
  have hh := h₁.sub h₂
  have he : (fun n => reconstructionFrame Φ hΦ T hT F x n -
      pastSmooth (infiniteKernelMeasure Φ hΦ T hT) (fun a => F (a, a)) x) =
      (fun n => (reconstructionFrame Φ hΦ T hT F x n -
        pastSmooth (dyadicKernelMeasure (kernelProfileMeasure Φ) T n) (fun a => F (a, a)) x) -
        (pastSmooth (infiniteKernelMeasure Φ hΦ T hT) (fun a => F (a, a)) x -
        pastSmooth (dyadicKernelMeasure (kernelProfileMeasure Φ) T n) (fun a => F (a, a)) x)) := by
    funext n
    ring
  have hz : Tendsto (fun n => reconstructionFrame Φ hΦ T hT F x n -
      pastSmooth (infiniteKernelMeasure Φ hΦ T hT) (fun a => F (a, a)) x) atTop (𝓝 0) := by
    rw [he]
    simpa only [sub_zero] using hh
  simpa only [zero_add, sub_add_cancel] using hz.add_const
    (pastSmooth (infiniteKernelMeasure Φ hΦ T hT) (fun a => F (a, a)) x)

end GlobalPhi43.MW20
