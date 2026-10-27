module

public import GlobalPhi43.MW20.KernelSourceNormBridges
public import GlobalPhi43.MW20.KernelSecondProduct

/-!
# The actual parent second-product tree norms on a local testing domain
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Set

/-- Restrict the canonical YV−C₂ norm, retaining its original scale range. -/
theorem recenteredASeminorm_testingKernel_le_sourceKernel
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {D E : Set ParabolicSpace} (hDE : D ⊆ E) (ε : ℝ) (Y V : ParabolicSpace → ℝ) (C₂ : ℝ) :
    recenteredASeminorm (mw20TestingKernel Φ hΦ) D ε Y V C₂ ≤
      recenteredASeminorm (sourceKernelFamily Φ hΦ) E ε Y V C₂ := by
  rw [sourceKernelFamily_eq_mw20TestingKernel]
  exact localTestSeminorm_mono_domain _ hDE (Ioo 0 1) (-4 * ε)
    (fun x y => (Y y - Y x) * V y - C₂)

/-- Restrict the canonical ZV−3C₂J norm without replacing J by V. -/
theorem recenteredDSeminorm_testingKernel_le_sourceKernel
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {D E : Set ParabolicSpace} (hDE : D ⊆ E) (ε : ℝ) (Z V J : ParabolicSpace → ℝ) (C₂ : ℝ) :
    recenteredDSeminorm (mw20TestingKernel Φ hΦ) D ε Z V J C₂ ≤
      recenteredDSeminorm (sourceKernelFamily Φ hΦ) E ε Z V J C₂ := by
  rw [sourceKernelFamily_eq_mw20TestingKernel]
  exact localTestSeminorm_mono_domain _ hDE (Ioo 0 1) (-(1 / 2) - 5 * ε)
    (fun x y => (Z y - Z x) * V y - 3 * C₂ * J y)

/-- The actual vector XV norm restricts in its base domain; no component
integrability or test estimate is assumed as an extra input. -/
theorem recenteredXVSeminorm_testingKernel_le_sourceKernel
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {D E : Set ParabolicSpace} (hDE : D ⊆ E) (ε : ℝ) (V : ParabolicSpace → ℝ) :
    recenteredXVSeminorm (mw20TestingKernel Φ hΦ) D ε V ≤
      recenteredXVSeminorm (sourceKernelFamily Φ hΦ) E ε V := by
  rw [sourceKernelFamily_eq_mw20TestingKernel]
  simp only [recenteredXVSeminorm, iSup_le_iff]
  intro x hx t ht
  exact le_iSup_of_le x (le_iSup_of_le (hDE hx)
    (le_iSup_of_le t (le_iSup_of_le ht le_rfl)))

end GlobalPhi43.MW20
