module

public import GlobalPhi43.MW20.KernelNegativeSeminorms

/-! Actual negative source norms are finite on compactly contained base
domains for continuous germs. No uniform bound in the source data is asserted. -/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Set
open scoped ENNReal

/-- The actual negative testing supremum admits a finite bound on every
compactly contained base domain. This follows from the true kernel support,
not continuity of a postulated scale family. -/
theorem mw20_localTestSeminorm_finite_bound (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (D s : Set ParabolicSpace) (hDs : D ⊆ s) (hs : IsCompact s)
    (I : Set ℝ) (hI : I ⊆ Ioc 0 1) {α : ℝ} (hα : α ≤ 0)
    (G : ParabolicSpace × ParabolicSpace → ℝ) (hG : Continuous G) :
    ∃ N : ℝ, 0 ≤ N ∧ localTestSeminorm (mw20TestingKernel Φ hΦ) D I α
      (fun x y => G (x, y)) ≤ ENNReal.ofReal N := by
  have hH : Continuous (fun p : ParabolicSpace × ParabolicSpace => G (p.1, p.1 + p.2)) :=
    hG.comp (continuous_fst.prodMk (continuous_fst.add continuous_snd))
  obtain ⟨M, hM⟩ := (hs.prod (isCompact_closedBall (0 : ParabolicSpace) 1)).exists_bound_of_continuousOn hH.continuousOn
  refine ⟨max M 0, le_max_right _ _, (localTestSeminorm_le_iff _ _ _ _ _ (le_max_right _ _)).2 ?_⟩
  intro x hx t htI
  have ht := (hI htI).1
  have ht₁ := (hI htI).2
  have := infiniteKernelMeasure_probability Φ hΦ ht ht₁
  rw [mw20TestingKernel_pos Φ hΦ ht]
  have htest : |pastSmooth (infiniteKernelMeasure Φ hΦ t ht) (fun y => G (x, y)) x| ≤ max M 0 := by
    have hb := norm_integral_le_of_norm_le_const (μ := infiniteKernelMeasure Φ hΦ t ht)
      (f := fun w => G (x, x + w)) (C := max M 0) (by
        filter_upwards [reconstruction_kernel_norm_support Φ hΦ ht ht₁] with w hw
        have hw₁ : w ∈ Metric.closedBall (0 : ParabolicSpace) 1 := by
          rw [Metric.mem_closedBall, dist_zero_right]
          exact hw.trans (max_le (by nlinarith) ht₁)
        exact (hM (x, w) ⟨hDs hx, hw₁⟩).trans (le_max_left _ _))
    simpa [pastSmooth, Real.norm_eq_abs] using hb
  have hp : t ^ (-α) ≤ 1 := Real.rpow_le_one ht.le ht₁ (neg_nonneg.2 hα)
  exact (mul_le_mul hp htest (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

/-- Finiteness of the actual extended negative norm, with no real-supremum
fallback convention and no separate finite-norm assumption. -/
theorem mw20_localTestSeminorm_ne_top (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (D s : Set ParabolicSpace) (hDs : D ⊆ s) (hs : IsCompact s)
    (I : Set ℝ) (hI : I ⊆ Ioc 0 1) {α : ℝ} (hα : α ≤ 0)
    (G : ParabolicSpace × ParabolicSpace → ℝ) (hG : Continuous G) :
    localTestSeminorm (mw20TestingKernel Φ hΦ) D I α (fun x y => G (x, y)) ≠ ⊤ := by
  obtain ⟨N, _, hN⟩ := mw20_localTestSeminorm_finite_bound Φ hΦ D s hDs hs I hI hα G hG
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hN

end GlobalPhi43.MW20
