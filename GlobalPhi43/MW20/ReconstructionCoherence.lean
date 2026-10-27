module

public import GlobalPhi43.MW20.ReconstructionFrameIncrement
public import GlobalPhi43.Local.SmoothingComparison

/-! The source coherence hypothesis pays the frame increment, with
exact parabolic radii and non-strict individual exponent comparisons. -/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Local

/-- The actual MW20 reconstruction frame satisfies the source-scale bound.
Open-ball coherence extends to the genuine kernel supports by continuity. -/
theorem reconstruction_source_frame_increment (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {T γ : ℝ} (hT : 0 < T) (hT₁ : T ≤ 1) (x : ParabolicSpace)
    (F : ParabolicSpace × ParabolicSpace → ℝ) (hF : Continuous F)
    (A : Finset ℝ) (C rate : ℝ → ℝ) (hC : ∀ β ∈ A, 0 ≤ C β)
    (hA : ∀ β ∈ A, β ≤ γ) (hrate : ∀ β ∈ A, γ ≤ rate β)
    (hcoh : ∀ t (ht : 0 < t), t < T →
      ∀ a ∈ pastBall x (T - t), ∀ b ∈ pastBall x (T - t),
        |pastSmooth (infiniteKernelMeasure Φ hΦ t ht) (fun y => F (a, y) - F (b, y)) b| ≤
          ∑ β ∈ A, C β * pdist a b ^ (rate β - β) * t ^ β) (n : ℕ) :
    |reconstructionFrame Φ hΦ T hT F x n - reconstructionFrame Φ hΦ T hT F x (n + 1)| ≤
      ∑ β ∈ A, C β * reconstructionScale T (n + 1) ^ rate β := by
  have := kernelProfileMeasure_probability Φ hΦ
  have := reconstructionTail_probability Φ hΦ hT hT₁ (n + 1)
  let t := reconstructionScale T (n + 1)
  have ht : 0 < t := reconstructionScale_pos hT (n + 1)
  have ht₁ : t ≤ 1 := reconstructionScale_le_one hT₁ (n + 1)
  have hhalf : t = reconstructionScale T n / 2 := reconstructionScale_succ T n
  have htT : t < T := by linarith [reconstructionScale_le hT.le n]
  have hs : T * (1 - 1 / (2 : ℝ) ^ n) = T - reconstructionScale T n := by
    unfold reconstructionScale
    ring
  apply reconstruction_frame_increment_le Φ hΦ hT hT₁ n F hF x
  filter_upwards [dyadicKernelMeasure_ae_past_radius (kernelProfileMeasure Φ) hT.le
    (kernelProfileMeasure_ae_parabolic Φ hΦ) n] with z hz
  rw [hs] at hz
  have hza : pdist x (x + z) ≤ T - t := by
    rw [pdist_add_right]
    linarith [hz.2, ht.le]
  have hzat : (x + z).1 ≤ x.1 := by simpa only [Prod.fst_add] using add_le_of_nonpos_right hz.1
  have hbound := tested_increment_bound_of_past_support A
    (dyadicKernelFactor (kernelProfileMeasure Φ) T n)
    (reconstructionTail Φ hΦ T hT (n + 1)) ht.le ht.le
    (dyadicKernelFactor_ae_parabolic Φ hΦ hT.le n)
    (reconstruction_kernel_norm_support Φ hΦ ht ht₁) F hF (x + z) C
    (fun β => rate β - β) id hC
    (fun β hβ => by linarith [hA β hβ, hrate β hβ]) (by
      intro v hvt hvd
      have hb : pdist x (x + z + v) ≤ T - t := by
        have hh := pdist_triangle x (x + z) (x + z + v)
        rw [pdist_add_right, pdist_add_right] at hh
        linarith [hz.2, hhalf]
      have hbt : (x + z + v).1 ≤ x.1 := by
        simp only [Prod.fst_add]
        linarith [hz.1]
      have hh := reconstruction_coherence_closed_ball Φ hΦ ht ht₁ (sub_pos.2 htT) x F hF
        A C rate hA hrate (hcoh t ht htT) hza hzat hb hbt
      simpa only [pastSmooth, reconstructionTail, pdist_add_right, id_eq, t] using hh)
  exact hbound.2.trans_eq (reconstruction_increment_scale_identity A C rate id ht)

end GlobalPhi43.MW20
