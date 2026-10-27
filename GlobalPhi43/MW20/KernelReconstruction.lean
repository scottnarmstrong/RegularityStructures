module

public import GlobalPhi43.MW20.ReconstructionCoherence
public import GlobalPhi43.MW20.Telescoping
public import GlobalPhi43.MW20.InfinitePastSmoothing

/-! Core reconstruction bound and the exact density pairing for the constructed past-looking kernel. -/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Local
open scoped ContDiff

/-- The complete reconstruction estimate, with an explicit constant
independent of the individual rates. Continuous germs already suffice. -/
theorem kernel_reconstruction_bound (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {γ T : ℝ} (hγ : 0 < γ) (hT : 0 < T) (hT₁ : T ≤ 1) (x : ParabolicSpace)
    (F : ParabolicSpace × ParabolicSpace → ℝ) (hF : Continuous F)
    (A : Finset ℝ) (C rate : ℝ → ℝ) (hC : ∀ β ∈ A, 0 ≤ C β)
    (hA : ∀ β ∈ A, β ≤ γ) (hrate : ∀ β ∈ A, γ ≤ rate β)
    (hcoh : ∀ t (ht : 0 < t), t < T →
      ∀ a ∈ pastBall x (T - t), ∀ b ∈ pastBall x (T - t),
        |pastSmooth (infiniteKernelMeasure Φ hΦ t ht) (fun y => F (a, y) - F (b, y)) b| ≤
          ∑ β ∈ A, C β * pdist a b ^ (rate β - β) * t ^ β) :
    |pastSmooth (infiniteKernelMeasure Φ hΦ T hT) (fun y => F (x, y) - F (y, y)) x| ≤
      (∑ β ∈ A, C β * T ^ rate β) / (1 - (1 / 2 : ℝ) ^ γ) := by
  have hb : ∀ β ∈ A, 0 ≤ C β * T ^ rate β := fun β hβ =>
    mul_nonneg (hC β hβ) (Real.rpow_nonneg hT.le _)
  have hi : ∀ n, |reconstructionFrame Φ hΦ T hT F x n -
      reconstructionFrame Φ hΦ T hT F x (n + 1)| ≤
      ∑ β ∈ A, (C β * T ^ rate β) * ((1 / 2 : ℝ) ^ rate β) ^ n := by
    intro n
    apply (reconstruction_source_frame_increment Φ hΦ hT hT₁ x F hF A C rate hC hA hrate hcoh n).trans
    apply Finset.sum_le_sum
    intro β hβ
    rw [reconstructionScale_rpow hT.le, pow_succ]
    have he : 0 ≤ rate β := hγ.le.trans (hrate β hβ)
    have hq : (1 / 2 : ℝ) ^ rate β ≤ 1 := Real.rpow_le_one (by norm_num) (by norm_num) he
    calc
      C β * (T ^ rate β * (((1 / 2 : ℝ) ^ rate β) ^ n * (1 / 2 : ℝ) ^ rate β)) =
          (C β * T ^ rate β) * ((1 / 2 : ℝ) ^ rate β) ^ n * (1 / 2 : ℝ) ^ rate β := by ring
      _ ≤ (C β * T ^ rate β) * ((1 / 2 : ℝ) ^ rate β) ^ n :=
        mul_le_of_le_one_right (by positivity [hC β hβ]) hq
  have ht := reconstruction_telescope_bound A (fun β => C β * T ^ rate β) rate hγ hb hrate hi
    (reconstruction_frame_tendsto Φ hΦ hT hT₁ F hF x)
  have hz : reconstructionFrame Φ hΦ T hT F x 0 =
      pastSmooth (infiniteKernelMeasure Φ hΦ T hT) (fun y => F (x, y)) x := by
    simp [reconstructionFrame, dyadicKernelMeasure, kernelMeasure, pastSmooth, reconstructionTail]
  rw [hz] at ht
  have hi₁ := reconstruction_kernel_section_integrable Φ hΦ hT hT₁ (fun y => F (x, y))
    (hF.comp (continuous_const.prodMk continuous_id)) x
  have hi₂ := reconstruction_kernel_section_integrable Φ hΦ hT hT₁ (fun y => F (y, y))
    (hF.comp (continuous_id.prodMk continuous_id)) x
  rwa [pastSmooth_sub_of_integrable _ _ _ x hi₁ hi₂]

/-- Measure and smooth-density tests agree for the actual MW20 kernel. -/
theorem reconstruction_pastSmooth_eq_density (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {t : ℝ} (ht : 0 < t) (ht₁ : t ≤ 1) (f : ParabolicSpace → ℝ) (x : ParabolicSpace) :
    pastSmooth (infiniteKernelMeasure Φ hΦ t ht) f x = infinitePastSmooth Φ hΦ t ht f x :=
  integral_infiniteKernelMeasure Φ hΦ ht ht₁ _

end GlobalPhi43.MW20
