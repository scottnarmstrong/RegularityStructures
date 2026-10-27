module

public import GlobalPhi43.MW20.ReconstructionKernelTests
public import GlobalPhi43.MW20.ReconstructionScales

/-! The diagonal approximation for the actual infinite MW20 kernels.
Smooth source sections are not assumed globally bounded; compact support
supplies integrability and compact-base uniform continuity supplies the limit. -/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Local Set Filter
open scoped Topology

/-- A local oscillation bounds the actual infinite-kernel diagonal error. -/
theorem reconstruction_kernel_diagonal_error_le (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {t : ℝ} (ht : 0 < t) (ht₁ : t ≤ 1)
    (F : ParabolicSpace × ParabolicSpace → ℝ) (hF : Continuous F) (x : ParabolicSpace)
    {ε : ℝ} (hosc : ∀ w, w.1 ≤ 0 → pdist 0 w ≤ t → |F (x, x + w) - F (x, x)| ≤ ε) :
    |pastSmooth (infiniteKernelMeasure Φ hΦ t ht) (fun y => F (x, y)) x - F (x, x)| ≤ ε := by
  have := infiniteKernelMeasure_probability Φ hΦ ht ht₁
  have hi := reconstruction_kernel_section_integrable Φ hΦ ht ht₁ (fun y => F (x, y))
    (hF.comp (continuous_const.prodMk continuous_id)) x
  have heq : pastSmooth (infiniteKernelMeasure Φ hΦ t ht) (fun y => F (x, y)) x - F (x, x) =
      ∫ w, (F (x, x + w) - F (x, x)) ∂infiniteKernelMeasure Φ hΦ t ht := by
    rw [integral_sub hi (integrable_const _)]
    simp [pastSmooth]
  rw [heq, ← Real.norm_eq_abs]
  have hb := norm_integral_le_of_norm_le_const (μ := infiniteKernelMeasure Φ hΦ t ht)
    (f := fun w => F (x, x + w) - F (x, x)) (C := ε) (by
      filter_upwards [infiniteKernelMeasure_ae_closedPast Φ hΦ ht ht₁] with w hw
      simpa only [Real.norm_eq_abs] using hosc w hw.1 hw.2)
  simpa using hb

/-- Uniform diagonal convergence on a compact base domain, derived from the
actual constructed kernels' probability and support properties. -/
theorem reconstruction_uniform_diagonal (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (t : ℕ → ℝ) (ht : ∀ n, 0 < t n) (ht₁ : ∀ n, t n ≤ 1)
    (hlim : Tendsto t atTop (𝓝 0))
    (F : ParabolicSpace × ParabolicSpace → ℝ) (hF : Continuous F)
    (s : Set ParabolicSpace) (hs : IsCompact s) :
    TendstoUniformlyOn (fun n x => pastSmooth (infiniteKernelMeasure Φ hΦ (t n) (ht n))
      (fun y => F (x, y)) x) (fun x => F (x, x)) atTop s := by
  have hG : Continuous (fun p : ParabolicSpace × ParabolicSpace => F (p.1, p.1 + p.2)) :=
    hF.comp (continuous_fst.prodMk (continuous_fst.add continuous_snd))
  have huc := (hs.prod (isCompact_closedBall (0 : ParabolicSpace) 1)).uniformContinuousOn_of_continuous hG.continuousOn
  apply Metric.tendstoUniformlyOn_iff.2
  intro ε hε
  obtain ⟨δ, hδ, hnear⟩ := Metric.uniformContinuousOn_iff.1 huc (ε / 2) (half_pos hε)
  filter_upwards [(Metric.tendsto_nhds.1 hlim) δ hδ] with n hn x hx
  have hn' : t n < δ := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos (ht n)] using hn
  have hb := reconstruction_kernel_diagonal_error_le Φ hΦ (ht n) (ht₁ n) F hF x
    (ε := ε / 2) (by
      intro w htime hdist
      have hmax : max ((t n) ^ 2) (t n) ≤ t n := max_le (by nlinarith [ht n, ht₁ n]) le_rfl
      have hw := (norm_le_of_pdist_zero_le (ht n).le hdist).trans hmax
      have hwball : w ∈ Metric.closedBall (0 : ParabolicSpace) 1 := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hw.trans (ht₁ n)
      have hpair : dist (x, w) (x, (0 : ParabolicSpace)) < δ := by
        simpa only [Prod.dist_eq, dist_self, dist_zero_right, max_eq_right (norm_nonneg w)] using hw.trans_lt hn'
      have hh := hnear (x, w) ⟨hx, hwball⟩ (x, 0) ⟨hx, by simp⟩ hpair
      simpa only [add_zero, Real.dist_eq] using hh.le)
  rw [Real.dist_eq, abs_sub_comm]
  exact hb.trans_lt (half_lt_self hε)

end GlobalPhi43.MW20
