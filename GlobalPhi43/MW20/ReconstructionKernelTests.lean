module

public import GlobalPhi43.MW20.KernelPastSupport
public import GlobalPhi43.MW20.ReconstructionIntegrals
public import GlobalPhi43.MW20.ReconstructionBallClosure
public import GlobalPhi43.MW20.DyadicKernelSupport

/-! Test continuity, integrability and boundary extension for the infinite
MW20 kernel, using its probability normalization and closed-past support. -/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Local Set

/-- Ambient compact support used only for topological/integrability steps. -/
theorem reconstruction_kernel_norm_support (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {t : ℝ} (ht : 0 < t) (ht₁ : t ≤ 1) :
    ∀ᵐ w ∂infiniteKernelMeasure Φ hΦ t ht, ‖w‖ ≤ max (t ^ 2) t := by
  filter_upwards [infiniteKernelMeasure_ae_closedPast Φ hΦ ht ht₁] with w hw
  exact norm_le_of_pdist_zero_le ht.le hw.2

/-- Every continuous source section is integrable against the actual kernel. -/
theorem reconstruction_kernel_section_integrable (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {t : ℝ} (ht : 0 < t) (ht₁ : t ≤ 1) (f : ParabolicSpace → ℝ)
    (hf : Continuous f) (x : ParabolicSpace) :
    Integrable (fun w => f (x + w)) (infiniteKernelMeasure Φ hΦ t ht) := by
  have := infiniteKernelMeasure_probability Φ hΦ ht ht₁
  exact compact_past_section_integrable _ (max (t ^ 2) t)
    (reconstruction_kernel_norm_support Φ hΦ ht ht₁) f hf x


/-- Continuous dependence of the actual tested diagonal on its base. -/
theorem reconstruction_kernel_diagonal_test_continuous (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {t : ℝ} (ht : 0 < t) (ht₁ : t ≤ 1)
    (F : ParabolicSpace × ParabolicSpace → ℝ) (hF : Continuous F) :
    Continuous (fun x => pastSmooth (infiniteKernelMeasure Φ hΦ t ht) (fun y => F (x, y)) x) := by
  have := infiniteKernelMeasure_probability Φ hΦ ht ht₁
  exact compact_measure_diagonal_test_continuous _ (max (t ^ 2) t)
    (reconstruction_kernel_norm_support Φ hΦ ht ht₁) F hF

/-- The exact source coherence test is continuous in both base points. -/
theorem reconstruction_kernel_germ_increment_continuous (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {t : ℝ} (ht : 0 < t) (ht₁ : t ≤ 1)
    (F : ParabolicSpace × ParabolicSpace → ℝ) (hF : Continuous F) :
    Continuous (fun p : ParabolicSpace × ParabolicSpace =>
      pastSmooth (infiniteKernelMeasure Φ hΦ t ht) (fun y => F (p.1, y) - F (p.2, y)) p.2) := by
  have := infiniteKernelMeasure_probability Φ hΦ ht ht₁
  exact compact_measure_germ_increment_continuous _ (max (t ^ 2) t)
    (reconstruction_kernel_norm_support Φ hΦ ht ht₁) F hF

/-- Extend the source's open-ball coherence hypothesis to the exact closed
past support points used by factorisation. Non-strict rate premises suffice. -/
theorem reconstruction_coherence_closed_ball (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {t r γ : ℝ} (ht : 0 < t) (ht₁ : t ≤ 1) (hr : 0 < r) (x : ParabolicSpace)
    (F : ParabolicSpace × ParabolicSpace → ℝ) (hF : Continuous F)
    (A : Finset ℝ) (C rate : ℝ → ℝ)
    (hA : ∀ β ∈ A, β ≤ γ) (hrate : ∀ β ∈ A, γ ≤ rate β)
    (hcoh : ∀ a ∈ pastBall x r, ∀ b ∈ pastBall x r,
      |pastSmooth (infiniteKernelMeasure Φ hΦ t ht) (fun y => F (a, y) - F (b, y)) b| ≤
        ∑ β ∈ A, C β * pdist a b ^ (rate β - β) * t ^ β)
    {a b : ParabolicSpace} (ha : pdist x a ≤ r) (hat : a.1 ≤ x.1)
    (hb : pdist x b ≤ r) (hbt : b.1 ≤ x.1) :
    |pastSmooth (infiniteKernelMeasure Φ hΦ t ht) (fun y => F (a, y) - F (b, y)) b| ≤
      ∑ β ∈ A, C β * pdist a b ^ (rate β - β) * t ^ β := by
  have hleft := (reconstruction_kernel_germ_increment_continuous Φ hΦ ht ht₁ F hF).abs
  have hpd : Continuous (fun p : ParabolicSpace × ParabolicSpace => pdist p.1 p.2) := by
    unfold pdist
    fun_prop
  have hright : Continuous (fun p : ParabolicSpace × ParabolicSpace =>
      ∑ β ∈ A, C β * pdist p.1 p.2 ^ (rate β - β) * t ^ β) := by
    apply continuous_finsetSum
    intro β hβ
    have he : 0 ≤ rate β - β := by linarith [hA β hβ, hrate β hβ]
    exact (continuous_const.mul ((Real.continuous_rpow_const he).comp hpd)).mul continuous_const
  have hp : (a, b) ∈ closure (pastBall x r ×ˢ pastBall x r) := by
    rw [closure_prod_eq]
    exact ⟨reconstruction_mem_closure_pastBall x a hr ha hat,
      reconstruction_mem_closure_pastBall x b hr hb hbt⟩
  exact le_on_closure (fun p hp => hcoh p.1 hp.1 p.2 hp.2)
    hleft.continuousOn hright.continuousOn hp

end GlobalPhi43.MW20
