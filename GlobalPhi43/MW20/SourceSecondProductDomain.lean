module

public import GlobalPhi43.MW20.SourceSecondProductRow
public import GlobalPhi43.MW20.AffineTestingDomains
public import GlobalPhi43.MW20.ScalarTestingDomains
public import GlobalPhi43.MW20.PastBallNormGeometry
public import GlobalPhi43.MW20.CylinderCoefficientBounds
public import GlobalPhi43.MW20.SecondProductSmallnessAlgebra
public import GlobalPhi43.MW20.SourceAffineFiniteness
public import GlobalPhi43.MW20.CoefficientHolderFiniteness
public import GlobalPhi43.MW20.ScalarSupNorm
public import GlobalPhi43.MW20.PastBallNormDomains

/-!
# The second product on common mixed-domain radius-local norms
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set
open scoped ContDiff

/-- The second-product row. Every local norm is its actual value and
is proved finite from the standing smooth fields. All four tree budgets
are at the same parent P_r, with their original counterterms and J/V fields. -/
theorem source_second_product_mixed_domain
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (v J Y Z V : ParabolicSpace → ℝ) (C₂ : ℝ)
    (hv : ContDiff ℝ ∞ v) (hJ : ContDiff ℝ ∞ J) (hY : ContDiff ℝ ∞ Y)
    (hZ : ContDiff ℝ ∞ Z) (hV : ContDiff ℝ ∞ V)
    {r d T ε c : ℝ} (hr : 0 ≤ r) (hd : 0 < d) (hT : 0 < T) (h2Td : 2 * T ≤ d)
    (hε : 0 < ε) (hsmall : ε < 1 / 14) (hc : 0 ≤ c)
    {x : ParabolicSpace} (hx : x ∈ Local.cylinderInterior r d)
    (hball : Local.pastBall x T ⊆ Local.cylinderInterior r d)
    (hbudgetA : recenteredASeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε Y V C₂ ≤
      ENNReal.ofReal (c * sourceSup v r ^ (2 - 4 * ε)))
    (hbudgetV : negativeTreeSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) (-1 - 2 * ε) V ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 - 2 * ε)))
    (hbudgetX : recenteredXVSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε V ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 - 2 * ε)))
    (hbudgetD : recenteredDSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε Z V J C₂ ≤
      ENNReal.ofReal (c * sourceSup v r ^ (5 / 2 - 5 * ε))) :
    let D := Local.cylinderInterior r d
    let M := sourceSup v r
    let Hv := localSourceHolder v (1 / 2 - 3 * ε) D d
    let HU := (radiusAffineSeminorm (sourceExpansion v Y Z) D (3 / 2 - 5 * ε) d).toReal
    let Hν := (localCoefficientHolderSeminorm (sourceAffineCoefficient v Y Z) D (1 / 2 - 5 * ε)).toReal
    let N := (localScalarSup (fun a => ‖sourceAffineCoefficient v Y Z a‖) D).toReal
    let μ := infiniteKernelMeasure Φ hΦ T hT
    |pastSmooth μ (fun y => (v y - v x) * V y) x +
      3 * C₂ * (pastSmooth μ v x + pastSmooth μ J x)| ≤ secondProductConstant ε * c *
      (T ^ (1 / 2 - 7 * ε) *
        (Hv * M ^ (2 - 4 * ε) + (HU + Hν) * M ^ (1 - 2 * ε)) +
        M ^ (5 / 2 - 5 * ε) * T ^ (-(1 / 2) - 5 * ε) +
        T ^ (-4 * ε) * M ^ (3 - 4 * ε) + N * M ^ (1 - 2 * ε) * T ^ (-2 * ε)) := by
  let D := Local.cylinderInterior r d
  have hd1 := (mixedInterior_depth_lt_one hr hx).le
  have hT1 : T < 1 := by linarith
  have hvreg := sourceCubicRegularity_of_contDiff (hv.of_le (by simp))
  have hM := sourceSup_nonneg_of_continuousOn_all hvreg.continuous hr
  have hbv := mixedInteriorHolder_bddAbove hvreg hr hd
    (show (1 / 2 : ℝ) - 3 * ε ≤ 1 by linarith) hd1
  have hdiam : ∀ a ∈ Local.pastBall x T, ∀ b ∈ Local.pastBall x T, Local.pdist a b ≤ d :=
    fun _ ha _ hb => (pastBall_pair_distance ha hb).trans h2Td
  have hHv := scalarHolderSeminorm_toReal_le_local_holder v hball hd1 hbv hdiam
  have hnU := source_expansion_radiusAffine_ne_top v Y Z hv hY hZ hr hd.le
    (by linarith : 0 ≤ (3 / 2 : ℝ) - 5 * ε) (by linarith : (3 / 2 : ℝ) - 5 * ε ≤ 2) d
  have hUnorm := localAffineSeminorm_le_radius_on_testing_domain (sourceExpansion v Y Z)
    (sourceExpansion_contDiff v Y Z hv hY hZ) (isOpen_cylinderInterior r d) hball
    (by linarith : 1 < (3 / 2 : ℝ) - 5 * ε) hd hdiam
  have hHU := ENNReal.toReal_mono hnU hUnorm
  have hDb : D ⊆ Metric.closedBall (0 : ParabolicSpace) 1 :=
    mixedInterior_subset_unit_closedBall hr hd.le
  have hnν := sourceAffineCoefficient_holder_ne_top v Y Z hv hY hZ D 1 hDb
    (by linarith : 0 ≤ 1 / 2 - 5 * ε) (by linarith : 1 / 2 - 5 * ε ≤ 1)
  have hHν := ENNReal.toReal_mono hnν
    (localCoefficientHolderSeminorm_mono (sourceAffineCoefficient v Y Z) (1 / 2 - 5 * ε) hball)
  have hνc := (sourceAffineCoefficient_contDiff v Y Z hv hY hZ).continuous
  have hnN := localScalarSup_ne_top (fun a => ‖sourceAffineCoefficient v Y Z a‖) hνc.norm
    D (Metric.closedBall 0 1) hDb (isCompact_closedBall _ _)
  have hN := ENNReal.toReal_mono hnN
    (localScalarSup_mono_domain (fun a => ‖sourceAffineCoefficient v Y Z a‖) hball)
  have hprod := mw20_row_4_3 Φ hΦ v J Y Z V C₂ hv hJ hY hZ hV hr hT hT1 hε hsmall hc x
    (fun a ha => mixedInterior_subset_base hd.le (hball ha)) hbudgetA hbudgetV hbudgetX hbudgetD
  have hK := (secondProductConstant_pos hsmall).le
  apply hprod.trans
  gcongr

end GlobalPhi43.MW20
