module

public import GlobalPhi43.MW20.InfiniteDiagonalApproximation

/-! Varying outer probability measures preserve the actual infinite-kernel
local diagonal limit. No convergence assumption on the outer measures is used. -/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Set Filter
open scoped Topology

/-- Integrate the actual infinite-kernel diagonal approximation against any
sequence of outer probability measures concentrated in a fixed compact set. -/
theorem reconstruction_outer_diagonal_limit (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (t : ℕ → ℝ) (ht : ∀ n, 0 < t n) (ht₁ : ∀ n, t n ≤ 1)
    (hlim : Tendsto t atTop (𝓝 0))
    (F : ParabolicSpace × ParabolicSpace → ℝ) (hF : Continuous F)
    (s : Set ParabolicSpace) (hs : IsCompact s)
    (ν : ℕ → Measure ParabolicSpace) [∀ n, IsProbabilityMeasure (ν n)]
    (hν : ∀ n, ∀ᵐ x ∂ν n, x ∈ s) :
    Tendsto (fun n =>
      (∫ x, pastSmooth (infiniteKernelMeasure Φ hΦ (t n) (ht n))
        (fun y => F (x, y)) x ∂ν n) - ∫ x, F (x, x) ∂ν n) atTop (𝓝 0) := by
  have hu := reconstruction_uniform_diagonal Φ hΦ t ht ht₁ hlim F hF s hs
  apply Metric.tendsto_nhds.2
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hu (ε / 2) (half_pos hε)] with n hn
  have hi := integrable_of_continuous_compact_ae (ν n) s hs (hν n) _
    (reconstruction_kernel_diagonal_test_continuous Φ hΦ (ht n) (ht₁ n) F hF)
  have hj := integrable_of_continuous_compact_ae (ν n) s hs (hν n) _
    (hF.comp (continuous_id.prodMk continuous_id))
  change Integrable (fun x => F (x, x)) (ν n) at hj
  rw [dist_zero_right, ← integral_sub hi hj]
  have hb := norm_integral_le_of_norm_le_const (μ := ν n)
    (f := fun x => pastSmooth (infiniteKernelMeasure Φ hΦ (t n) (ht n))
      (fun y => F (x, y)) x - F (x, x)) (C := ε / 2) (by
      filter_upwards [hν n] with x hx
      simpa only [Real.norm_eq_abs, Real.dist_eq, abs_sub_comm] using (hn x hx).le)
  apply lt_of_le_of_lt _ (half_lt_self hε)
  simpa using hb

end GlobalPhi43.MW20
