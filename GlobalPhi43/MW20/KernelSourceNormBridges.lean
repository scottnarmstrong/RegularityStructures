module

public import GlobalPhi43.MW20.SourceKernelTreeTests
public import GlobalPhi43.MW20.KernelNegativeSeminorms
public import GlobalPhi43.MW20.SourceNormDomains
public import GlobalPhi43.MW20.LocalSourceHolder
public import Mathlib.Basic.ENNReal.Real

/-!
# Parent source norms in the MW20 product estimates
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Set

/-- The two positive-scale source interfaces are the very same measure family. -/
theorem sourceKernelFamily_eq_mw20TestingKernel (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ) :
    sourceKernelFamily Φ hΦ = mw20TestingKernel Φ hΦ := by
  funext t
  simp only [sourceKernelFamily, mw20TestingKernel]

/-- The J norm on a testing ball is controlled by the actual parent norm. -/
theorem negativeTreeSeminorm_testingKernel_le_sourceKernel
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {D E : Set ParabolicSpace} (hDE : D ⊆ E) (α : ℝ) (J : ParabolicSpace → ℝ) :
    negativeTreeSeminorm (mw20TestingKernel Φ hΦ) D α J ≤
      negativeTreeSeminorm (sourceKernelFamily Φ hΦ) E α J := by
  rw [sourceKernelFamily_eq_mw20TestingKernel]
  exact localTestSeminorm_mono_domain _ hDE (Ioc 0 1) α (fun _ => J)

/-- Restriction of the canonical recentered ZJ norm preserves its sign,
scale endpoints and parent allowance. -/
theorem recenteredBSeminorm_testingKernel_le_sourceKernel
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {D E : Set ParabolicSpace} (hDE : D ⊆ E) (ε : ℝ) (Z J : ParabolicSpace → ℝ) :
    recenteredBSeminorm (mw20TestingKernel Φ hΦ) D ε Z J ≤
      recenteredBSeminorm (sourceKernelFamily Φ hΦ) E ε Z J := by
  rw [sourceKernelFamily_eq_mw20TestingKernel]
  exact localTestSeminorm_mono_domain _ hDE (Ioo 0 1) (-4 * ε)
    (fun x y => (Z y - Z x) * J y)

end GlobalPhi43.MW20
