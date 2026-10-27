module

public import GlobalPhi43.MW20.KernelCoordinateSeminorm

/-! Boundary base-point testing for the source XV seminorm. This retains the
same actual vector-norm coefficient; it does not enlarge a source domain. -/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Set
open scoped ENNReal

/-- The component XV test extends to closure base points with its original
vector-norm bound, using actual compact-kernel continuity and integrability. -/
theorem coordinate_test_bound_of_mem_closure (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (D : Set ParabolicSpace) (ε : ℝ) (V : ParabolicSpace → ℝ) (hV : Continuous V)
    {N : ℝ} (hN : 0 ≤ N)
    (hnorm : recenteredXVSeminorm (mw20TestingKernel Φ hΦ) D ε V ≤ ENNReal.ofReal N)
    {x : ParabolicSpace} (hx : x ∈ closure D) {t : ℝ} (ht : 0 < t) (ht₁ : t < 1) (i : Fin 3) :
    |pastSmooth (infiniteKernelMeasure Φ hΦ t ht) (fun y => (y.2 i - x.2 i) * V y) x| ≤
      N * t ^ (-2 * ε) := by
  have hG : Continuous (fun p : ParabolicSpace × ParabolicSpace => (p.2.2 i - p.1.2 i) * V p.2) := by fun_prop
  have hc := (reconstruction_kernel_diagonal_test_continuous Φ hΦ ht ht₁.le _ hG).abs
  apply le_on_closure (s := D) _ hc.continuousOn continuous_const.continuousOn hx
  intro a ha
  have hb := recenteredXVSeminorm_component_test_bound (mw20TestingKernel Φ hΦ) D ε V hN hnorm ha ht ht₁
    (mw20_coordinateTree_integrable Φ hΦ V hV a ht ht₁.le) i
  rwa [mw20TestingKernel_pos Φ hΦ ht] at hb

end GlobalPhi43.MW20
