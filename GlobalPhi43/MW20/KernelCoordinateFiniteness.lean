module

public import GlobalPhi43.MW20.KernelCoordinateSeminorm

/-! Finiteness of the actual coordinate-vector source norm on bounded base
domains. This does not assume any regularity of a postulated kernel family. -/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Set
open scoped ENNReal

/-- Compact-kernel vector tests give a finite literal XV source seminorm. -/
theorem mw20_recenteredXV_finite_bound (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (D s : Set ParabolicSpace) (hDs : D ⊆ s) (hs : IsCompact s)
    {ε : ℝ} (hε : 0 ≤ ε) (V : ParabolicSpace → ℝ) (hV : Continuous V) :
    ∃ N : ℝ, 0 ≤ N ∧ recenteredXVSeminorm (mw20TestingKernel Φ hΦ) D ε V ≤ ENNReal.ofReal N := by
  have hG : Continuous (fun p : ParabolicSpace × ParabolicSpace => V (p.1 + p.2) • p.2.2) := by fun_prop
  obtain ⟨M, hM⟩ := (hs.prod (isCompact_closedBall (0 : ParabolicSpace) 1)).exists_bound_of_continuousOn hG.continuousOn
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  unfold recenteredXVSeminorm
  refine iSup_le fun x => iSup_le fun hx => iSup_le fun t => iSup_le fun ht => ?_
  apply ENNReal.ofReal_le_ofReal
  have := infiniteKernelMeasure_probability Φ hΦ ht.1 ht.2.le
  have htest : ‖coordinateTreeTest (mw20TestingKernel Φ hΦ) V t x‖ ≤ max M 0 := by
    unfold coordinateTreeTest
    rw [mw20TestingKernel_pos Φ hΦ ht.1]
    have hb := norm_integral_le_of_norm_le_const (μ := infiniteKernelMeasure Φ hΦ t ht.1)
      (f := fun w => V (x + w) • w.2) (C := max M 0) (by
        filter_upwards [reconstruction_kernel_norm_support Φ hΦ ht.1 ht.2.le] with w hw
        have hw₁ : w ∈ Metric.closedBall (0 : ParabolicSpace) 1 := by
          rw [Metric.mem_closedBall, dist_zero_right]
          exact hw.trans (max_le (by nlinarith [ht.1, ht.2]) ht.2.le)
        exact (hM (x, w) ⟨hDs hx, hw₁⟩).trans (le_max_left _ _))
    simpa using hb
  have hp : t ^ (2 * ε) ≤ 1 := Real.rpow_le_one ht.1.le ht.2.le (by positivity)
  exact (mul_le_mul hp htest (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

/-- XV norm finiteness is derived from source continuity and compact
containment, rather than imposed as an auxiliary analytical hypothesis. -/
theorem mw20_recenteredXV_ne_top (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (D s : Set ParabolicSpace) (hDs : D ⊆ s) (hs : IsCompact s)
    {ε : ℝ} (hε : 0 ≤ ε) (V : ParabolicSpace → ℝ) (hV : Continuous V) :
    recenteredXVSeminorm (mw20TestingKernel Φ hΦ) D ε V ≠ ⊤ := by
  obtain ⟨N, _, hN⟩ := mw20_recenteredXV_finite_bound Φ hΦ D s hDs hs hε V hV
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hN

end GlobalPhi43.MW20
