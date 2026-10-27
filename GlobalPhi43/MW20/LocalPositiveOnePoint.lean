module

public import GlobalPhi43.MW20.LocalPositiveForcing
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
public import GlobalPhi43.MW20.OnePointBudgetScale
public import GlobalPhi43.MW20.SourceSchauderExponents
public import GlobalPhi43.MW20.SourceOnePointCoefficient

/-! The actual formal forcing supremum and its one-point rate, without
PDE hypotheses or an enlargement of the radius-local affine norm. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set
open scoped ContDiff

theorem source_formal_one_point_positive
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
    {x : ParabolicSpace} (hx : x ∈ Local.cylinderInterior r d)
    (hball : Local.pastBall x (L + T) ⊆ Local.cylinderInterior r d) :
    let Q := localScalarSup (sourceFormalForcingAverage Φ hΦ v J V C₂ T hT x) (Local.pastBall x L)
    Q ≠ ⊤ ∧ T ^ 2 * Q.toReal ≤ sourceOnePointCoefficient v Y Z ε r d L c *
        (∑ a ∈ sourceSchauderExponents ε, T ^ a * L ^ ((3 / 2 - 5 * ε) - a)) := by
  let D := Local.cylinderInterior r d
  let M := sourceSup v r
  let H := localSourceHolder (fun a => v a + Z a) (1 - 2 * ε) D d
  let Hv := localSourceHolder v (1 / 2 - 3 * ε) D d
  let HU := (radiusAffineSeminorm (sourceExpansion v Y Z) D (3 / 2 - 5 * ε) d).toReal
  let Hν := (localCoefficientHolderSeminorm (sourceAffineCoefficient v Y Z) D (1 / 2 - 5 * ε)).toReal
  let N := (localScalarSup (fun a => ‖sourceAffineCoefficient v Y Z a‖) D).toReal
  let Q := localScalarSup (sourceFormalForcingAverage Φ hΦ v J V C₂ T hT x) (Local.pastBall x L)
  let C := smallScaleForcingConstant ε
  let F := M ^ 3 + L ^ (1 / 2 - 3 * ε) * T ^ (-1 - 2 * ε) * c * Hv * M ^ (1 - 2 * ε) +
    c * sourceFirstProductBudget ε T M H Hv + c * sourceSecondProductBudget ε T M Hv HU Hν N
  have hvreg := sourceCubicRegularity_of_contDiff (hv.of_le (by simp))
  have hsreg := sourceCubicRegularity_of_contDiff ((hv.add hZ).of_le (by simp))
  have hd1 := (mixedInterior_depth_lt_one hr hx).le
  have hM : 0 ≤ M := sourceSup_nonneg_of_continuousOn_all hvreg.continuous hr
  have hH : 0 ≤ H := localSourceHolder_nonneg
    (mixedInteriorHolder_bddAbove hsreg hr hd (show 1 - 2 * ε ≤ 1 by linarith) hd1)
  have hHv : 0 ≤ Hv := localSourceHolder_nonneg
    (mixedInteriorHolder_bddAbove hvreg hr hd (show (1 / 2 : ℝ) - 3 * ε ≤ 1 by linarith) hd1)
  have hHU : 0 ≤ HU := ENNReal.toReal_nonneg
  have hHν : 0 ≤ Hν := ENNReal.toReal_nonneg
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  have hL : 0 ≤ L := hT.le.trans hTL
  have hF : 0 ≤ F := by dsimp only [F, sourceFirstProductBudget, sourceSecondProductBudget]; positivity
  have hC : 0 ≤ C := by
    have hK₁ := (firstProductConstant_pos hsmall).le
    have hK₂ := (secondProductConstant_pos hsmall).le
    dsimp only [C, smallScaleForcingConstant]
    positivity
  have hnorm : Q ≤ ENNReal.ofReal (C*F) := by
    simp only [Q, localScalarSup, iSup_le_iff]
    intro y hy
    exact ENNReal.ofReal_le_ofReal (source_formal_forcing_bound_positive Φ hΦ v J Y Z V C₂
      hv hJ hY hZ hV hr hd hT hTL hLd hε hsmall hc hc1
      hbudgetZ hbudgetJ hbudgetB hbudgetA hbudgetV hbudgetX hbudgetD hx hball hy)
  have hfinite := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hnorm
  have hreal : Q.toReal ≤ C * F := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hnorm
    rwa [ENNReal.toReal_ofReal (mul_nonneg hC hF)] at hh
  have hscale := source_small_scale_budget_heat_scale hT hTL hε.le hsmall hM hH hHv hHU hHν hN hc
  change T ^ 2 * F ≤ sourceOnePointMajorant ε L M H Hv HU Hν N c *
    (T ^ (3 / 2 - 5 * ε) + T ^ (1 - 2 * ε) * L ^ (1 / 2 - 3 * ε)) at hscale
  have hmajorant := sourceOnePointMajorant_nonneg (ε := ε) hL hM hH hHv hHU hHν hN hc
  have hrates := sourceSchauderExponents_two_le hT.le hL hε.le hsmall
  change Q ≠ ⊤ ∧ T ^ 2 * Q.toReal ≤ C * sourceOnePointMajorant ε L M H Hv HU Hν N c *
    (∑ a ∈ sourceSchauderExponents ε, T ^ a * L ^ ((3 / 2 - 5 * ε) - a))
  refine ⟨hfinite, ?_⟩
  calc
    T ^ 2 * Q.toReal ≤ T ^ 2 * (C * F) := mul_le_mul_of_nonneg_left hreal (sq_nonneg T)
    _ = C * (T ^ 2 * F) := by ring
    _ ≤ C * (sourceOnePointMajorant ε L M H Hv HU Hν N c *
        (T ^ (3 / 2 - 5 * ε) + T ^ (1 - 2 * ε) * L ^ (1 / 2 - 3 * ε))) :=
      mul_le_mul_of_nonneg_left hscale hC
    _ ≤ C * (sourceOnePointMajorant ε L M H Hv HU Hν N c *
        (∑ a ∈ sourceSchauderExponents ε, T ^ a * L ^ ((3 / 2 - 5 * ε) - a))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrates hmajorant) hC
    _ = _ := by ring


end GlobalPhi43.MW20
