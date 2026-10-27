module

public import GlobalPhi43.MW20.KernelSecondProductAssembly
public import GlobalPhi43.MW20.KernelSecondConsumer
public import GlobalPhi43.MW20.SecondProductBudget

/-! The literal signed MW20 (2.33) estimate with actual kernel tests and
source norm controls. The coefficient is the optimal diagonal derivative. -/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Local Set
open scoped ENNReal ContDiff

/-- Full Lemma 2.10 estimate under actual source norm controls, with one
comparison constant depending only on epsilon and the literal separated LHS. -/
theorem mw20_lemma_2_10_of_norm_bounds (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (v J Y Z V : ParabolicSpace → ℝ) (C₂ : ℝ)
    (hv : ContDiff ℝ ∞ v) (hJ : ContDiff ℝ ∞ J) (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z) (hV : ContDiff ℝ ∞ V)
    (x : ParabolicSpace) {T ε : ℝ} (hT : 0 < T) (hT₁ : T < 1)
    (hε : 0 < ε) (hsmall : ε < 1 / 14)
    {Hv HU Hν NA NV NX : ℝ} (hHv : 0 ≤ Hv) (hHU : 0 ≤ HU) (hHν : 0 ≤ Hν)
    (hNA : 0 ≤ NA) (hNV : 0 ≤ NV) (hNX : 0 ≤ NX)
    (hvnorm : scalarHolderSeminorm v (pastBall x T) (1 / 2 - 3 * ε) ≤ ENNReal.ofReal Hv)
    (hUnorm : localAffineSeminorm (sourceExpansion v Y Z) (pastBall x T) (3 / 2 - 5 * ε) ≤ ENNReal.ofReal HU)
    (hνnorm : localCoefficientHolderSeminorm (sourceAffineCoefficient v Y Z) (pastBall x T)
      (1 / 2 - 5 * ε) ≤ ENNReal.ofReal Hν)
    (hAnorm : recenteredASeminorm (mw20TestingKernel Φ hΦ) (pastBall x T) ε Y V C₂ ≤ ENNReal.ofReal NA)
    (hVnorm : negativeTreeSeminorm (mw20TestingKernel Φ hΦ) (pastBall x T) (-1 - 2 * ε) V ≤ ENNReal.ofReal NV)
    (hXnorm : recenteredXVSeminorm (mw20TestingKernel Φ hΦ) (pastBall x T) ε V ≤ ENNReal.ofReal NX)
    {M N ND : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) (hND : 0 ≤ ND)
    (hsup : ∀ a ∈ pastBall x T, |v a| ≤ M)
    (hsupν : ∀ a ∈ pastBall x T, ‖sourceAffineCoefficient v Y Z a‖ ≤ N)
    (hDnorm : recenteredDSeminorm (mw20TestingKernel Φ hΦ) (pastBall x T) ε Z V J C₂ ≤ ENNReal.ofReal ND) :
    |infinitePastSmooth Φ hΦ T hT (fun y => (v y - v x) * V y) x +
      3 * C₂ * (infinitePastSmooth Φ hΦ T hT v x + infinitePastSmooth Φ hΦ T hT J x)| ≤
    secondProductConstant ε *
      (T ^ (1 / 2 - 7 * ε) * (Hv * NA + HU * NV + Hν * NX) +
        ND * T ^ (-(1 / 2) - 5 * ε) + T ^ (-4 * ε) * M * NA + N * NX * T ^ (-2 * ε)) := by
  have hh := kernel_secondProduct_product_bound Φ hΦ v J Y Z V C₂ hv hJ hY hZ hV x hT hT₁ hε hsmall
    hHv hHU hHν hNA hNV hNX hvnorm hUnorm hνnorm hAnorm hVnorm hXnorm hND hsup hsupν hDnorm
  rw [pastSmooth_second_consumer_separated Φ hΦ hT hT₁.le v J V hv.continuous hJ.continuous hV.continuous C₂ x] at hh
  simp_rw [reconstruction_pastSmooth_eq_density Φ hΦ hT hT₁.le] at hh
  exact hh.trans (secondProduct_budget_le hT hsmall hHv hHU hHν hNA hNV hNX hM hN hND)

end GlobalPhi43.MW20
