module

public import GlobalPhi43.MW20.FormalForcingComponents
public import GlobalPhi43.MW20.LocalPositiveFirstProduct
public import GlobalPhi43.MW20.SourceExpansionHeat
public import GlobalPhi43.MW20.GlobalHeatSmoothing
public import GlobalPhi43.MW20.PastBallTesting
public import GlobalPhi43.MW20.LocalSourcePairNorms
public import GlobalPhi43.MW20.SourceTestingCube
public import GlobalPhi43.MW20.SourceKernelTreeTests
public import GlobalPhi43.MW20.MixedInteriorHolder
public import GlobalPhi43.MW20.ExpansionForcingAlgebra
public import GlobalPhi43.MW20.KernelFirstProduct
public import GlobalPhi43.MW20.ScalarHolderFiniteness
public import GlobalPhi43.MW20.PastBallNormDomains
public import GlobalPhi43.MW20.KernelSourceNormBridges
public import GlobalPhi43.MW20.FirstProductSmallnessAlgebra
public import GlobalPhi43.MW20.ScalarTestingDomains
public import GlobalPhi43.MW20.PastBallNormGeometry
public import GlobalPhi43.MW20.SourceSecondProductDomain
public import GlobalPhi43.MW20.SmallScaleForcingBudget

/-! Formal forcing bound on actual local norms; no zero-defect PDE premise. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set
open scoped ContDiff

theorem source_formal_forcing_bound_positive
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (v J Y Z V : ParabolicSpace → ℝ) (C₂ : ℝ)
    (hv : ContDiff ℝ ∞ v) (hJ : ContDiff ℝ ∞ J) (hY : ContDiff ℝ ∞ Y)
    (hZ : ContDiff ℝ ∞ Z) (hV : ContDiff ℝ ∞ V)
    {r d T L ε c : ℝ} (hr : 0 ≤ r) (hd : 0 < d) (hT : 0 < T)
    (hTL : T ≤ L) (hLd : L ≤ d / 2) (hε : 0 < ε) (hsmall : ε < 1 / 14)
    (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hbudgetZ : parabolicHolderSeminorm (1 / 2 - 3 * ε) (parabolicClosedNbhd mwCylinder 1) Z ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 + (1 / 2 - 3 * ε))))
    (hbudgetJ : negativeTreeSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r)
      (-(1 / 2) - ε) J ≤ ENNReal.ofReal (c * sourceSup v r ^ (1 / 2 - ε)))
    (hbudgetB : recenteredBSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε Z J ≤
      ENNReal.ofReal (c * sourceSup v r ^ (2 - 4 * ε)))
    (hbudgetA : recenteredASeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε Y V C₂ ≤
      ENNReal.ofReal (c * sourceSup v r ^ (2 - 4 * ε)))
    (hbudgetV : negativeTreeSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) (-1 - 2 * ε) V ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 - 2 * ε)))
    (hbudgetX : recenteredXVSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε V ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 - 2 * ε)))
    (hbudgetD : recenteredDSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε Z V J C₂ ≤
      ENNReal.ofReal (c * sourceSup v r ^ (5 / 2 - 5 * ε)))
    {x y : ParabolicSpace} (hx : x ∈ Local.cylinderInterior r d)
    (hball : Local.pastBall x (L + T) ⊆ Local.cylinderInterior r d)
    (hy : y ∈ Local.pastBall x L) :
    let D := Local.cylinderInterior r d
    let M := sourceSup v r
    let H := localSourceHolder (fun a => v a + Z a) (1 - 2 * ε) D d
    let Hv := localSourceHolder v (1 / 2 - 3 * ε) D d
    let HU := (radiusAffineSeminorm (sourceExpansion v Y Z) D (3 / 2 - 5 * ε) d).toReal
    let Hν := (localCoefficientHolderSeminorm (sourceAffineCoefficient v Y Z) D (1 / 2 - 5 * ε)).toReal
    let N := (localScalarSup (fun a => ‖sourceAffineCoefficient v Y Z a‖) D).toReal
    |sourceFormalForcingAverage Φ hΦ v J V C₂ T hT x y| ≤ smallScaleForcingConstant ε *
      (M ^ 3 + L ^ (1 / 2 - 3 * ε) * T ^ (-1 - 2 * ε) * c * Hv * M ^ (1 - 2 * ε) +
        c * sourceFirstProductBudget ε T M H Hv + c * sourceSecondProductBudget ε T M Hv HU Hν N) := by
  let D := Local.cylinderInterior r d
  let M := sourceSup v r
  let H := localSourceHolder (fun a => v a + Z a) (1 - 2 * ε) D d
  let Hv := localSourceHolder v (1 / 2 - 3 * ε) D d
  let HU := (radiusAffineSeminorm (sourceExpansion v Y Z) D (3 / 2 - 5 * ε) d).toReal
  let Hν := (localCoefficientHolderSeminorm (sourceAffineCoefficient v Y Z) D (1 / 2 - 5 * ε)).toReal
  let N := (localScalarSup (fun a => ‖sourceAffineCoefficient v Y Z a‖) D).toReal
  have hd1 := (mixedInterior_depth_lt_one hr hx).le
  have h2Td : 2 * T ≤ d := by linarith
  have hL : 0 ≤ L := hT.le.trans hTL
  have hT1 : T < 1 := by linarith
  have hyD : y ∈ D := hball ⟨by linarith [hy.1], hy.2⟩
  have hBy : Local.pastBall y T ⊆ D := (pastBall_nested_subset hy).trans hball
  have hvreg := sourceCubicRegularity_of_contDiff (hv.of_le (by simp))
  have hsreg := sourceCubicRegularity_of_contDiff ((hv.add hZ).of_le (by simp))
  have hM : 0 ≤ M := sourceSup_nonneg_of_continuousOn_all hvreg.continuous hr
  have hHv : 0 ≤ Hv := localSourceHolder_nonneg
    (mixedInteriorHolder_bddAbove hvreg hr hd (show (1 / 2 : ℝ) - 3 * ε ≤ 1 by linarith) hd1)
  have hH : 0 ≤ H := localSourceHolder_nonneg
    (mixedInteriorHolder_bddAbove hsreg hr hd (show 1 - 2 * ε ≤ 1 by linarith) hd1)
  have hHU : 0 ≤ HU := ENNReal.toReal_nonneg
  have hHν : 0 ≤ Hν := ENNReal.toReal_nonneg
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  have hF₁ : 0 ≤ sourceFirstProductBudget ε T M H Hv := by unfold sourceFirstProductBudget; positivity
  have hF₂ : 0 ≤ sourceSecondProductBudget ε T M Hv HU Hν N := by unfold sourceSecondProductBudget; positivity
  have hforce := source_formal_forcing_components Φ hΦ v J V hv
    hJ.continuous.continuousOn hV.continuous.continuousOn C₂ hT hT1.le hr hd
    (by linarith : L ≤ d) hd1 hε hsmall hc hbudgetV hx hball hy
  have hp₁ := source_first_product_mixed_domain_positive Φ hΦ v Z J hv hZ hJ hr hd hT h2Td
    hε.le hsmall hc hc1 hyD hBy hbudgetZ hbudgetJ hbudgetB
  have hp₂ := source_second_product_mixed_domain Φ hΦ v J Y Z V C₂ hv hJ hY hZ hV hr hd hT h2Td
    hε hsmall hc hyD hBy hbudgetA hbudgetV hbudgetX hbudgetD
  apply small_scale_forcing_assemble hsmall (pow_nonneg hM 3) (by positivity) hF₁ hF₂ hc hforce
  · exact hp₁
  · exact hp₂


end GlobalPhi43.MW20
