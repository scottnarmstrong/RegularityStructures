module

public import GlobalPhi43.MW20.KernelNegativeSeminorms
public import GlobalPhi43.MW20.ScalarHolderSeminorm

/-! Extend literal source-norm bounds to the boundary points tested by
reconstruction. The centre of a strict past ball is a closure point, so this
step is necessary even for smooth fields. -/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Local Set
open scoped ENNReal

/-- Continuous source fields inherit a local supremum bound at closure points. -/
theorem source_sup_bound_closure (f : ParabolicSpace → ℝ) (hf : Continuous f)
    (D : Set ParabolicSpace) {M : ℝ} (hM : ∀ y ∈ D, |f y| ≤ M)
    {x : ParabolicSpace} (hx : x ∈ closure D) : |f x| ≤ M :=
  le_on_closure hM hf.abs.continuousOn continuous_const.continuousOn hx

/-- Actual local negative germ tests extend to closure base points because
compactly supported testing of a continuous germ is continuous in its base. -/
theorem mw20_localTestSeminorm_closure_test_bound (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (D : Set ParabolicSpace) (I : Set ℝ) (α : ℝ)
    (G : ParabolicSpace × ParabolicSpace → ℝ) (hG : Continuous G) {N : ℝ} (hN : 0 ≤ N)
    (hnorm : localTestSeminorm (mw20TestingKernel Φ hΦ) D I α
      (fun x y => G (x, y)) ≤ ENNReal.ofReal N)
    {x : ParabolicSpace} (hx : x ∈ closure D) {t : ℝ} (ht : 0 < t) (ht₁ : t ≤ 1) (htI : t ∈ I) :
    |infinitePastSmooth Φ hΦ t ht (fun y => G (x, y)) x| ≤ N * t ^ α := by
  have hc := (reconstruction_kernel_diagonal_test_continuous Φ hΦ ht ht₁ G hG).abs
  have hb : |pastSmooth (infiniteKernelMeasure Φ hΦ t ht) (fun y => G (x, y)) x| ≤ N * t ^ α := by
    apply le_on_closure (s := D) _ hc.continuousOn continuous_const.continuousOn hx
    intro y hy
    have hh := localTestSeminorm_test_bound (mw20TestingKernel Φ hΦ) D I α
      (fun x y => G (x, y)) hN hnorm hy ht htI
    rwa [mw20TestingKernel_pos Φ hΦ ht] at hh
  rwa [reconstruction_pastSmooth_eq_density Φ hΦ ht ht₁] at hb

end GlobalPhi43.MW20
