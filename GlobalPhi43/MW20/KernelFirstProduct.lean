module

public import GlobalPhi43.MW20.KernelFirstProductAssembly
public import GlobalPhi43.MW20.FirstProductBudget

/-! MW20 (2.32), with the actual tree factor and literal four budgets.
The source seminorm inputs are expressed as upper bounds on the existing
extended norms, so zero tree coefficients require no positivity padding. -/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Local Set
open scoped ENNReal ContDiff

/-- The complete first-product estimate with actual source norm controls.
K is the explicit firstProductConstant depending only on epsilon. -/
theorem mw20_lemma_2_9_of_norm_bounds (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (v Z J : ParabolicSpace → ℝ) (hv : ContDiff ℝ ∞ v) (hZ : ContDiff ℝ ∞ Z) (hJ : ContDiff ℝ ∞ J)
    (x : ParabolicSpace) {T ε : ℝ} (hT : 0 < T) (hT₁ : T < 1)
    (hε : 0 ≤ ε) (hsmall : ε < 1 / 14)
    {M H Hv HZ NJ NB : ℝ} (hM : 0 ≤ M) (hH : 0 ≤ H) (hHv : 0 ≤ Hv) (hHZ : 0 ≤ HZ)
    (hNJ : 0 ≤ NJ) (hNB : 0 ≤ NB) (hsup : ∀ a ∈ pastBall x T, |v a| ≤ M)
    (hplus : scalarHolderSeminorm (fun y => v y + Z y) (pastBall x T) (1 - 2 * ε) ≤ ENNReal.ofReal H)
    (hvnorm : scalarHolderSeminorm v (pastBall x T) (1 / 2 - 3 * ε) ≤ ENNReal.ofReal Hv)
    (hZnorm : scalarHolderSeminorm Z (pastBall x T) (1 / 2 - 3 * ε) ≤ ENNReal.ofReal HZ)
    (hJnorm : negativeTreeSeminorm (mw20TestingKernel Φ hΦ) (pastBall x T) (-(1 / 2) - ε) J ≤ ENNReal.ofReal NJ)
    (hBnorm : recenteredBSeminorm (mw20TestingKernel Φ hΦ) (pastBall x T) ε Z J ≤ ENNReal.ofReal NB) :
    |infinitePastSmooth Φ hΦ T hT (fun y => v y ^ 2 * J y) x| ≤
      firstProductConstant ε *
        (T ^ (1 / 2 - 3 * ε) * M * H * NJ +
          T ^ (1 / 2 - 7 * ε) * Hv * (HZ * NJ + NB) +
          M ^ 2 * NJ * T ^ (-(1 / 2) - ε) + M * NB * T ^ (-4 * ε)) := by
  have hh := kernel_firstProduct_product_bound Φ hΦ v Z J hv hZ hJ x hT hT₁ hε hsmall
    hM hH hHv hHZ hNJ hNB hsup hplus hvnorm hZnorm hJnorm hBnorm
  rw [reconstruction_pastSmooth_eq_density Φ hΦ hT hT₁.le] at hh
  exact hh.trans (firstProduct_budget_le hT hsmall hM hH hHv hHZ hNJ hNB)

end GlobalPhi43.MW20
