module

public import GlobalPhi43.MW20.KernelSecondNormBridges
public import GlobalPhi43.MW20.SecondProductSmallnessAlgebra
public import GlobalPhi43.MW20.SourceAffineFiniteness
public import GlobalPhi43.MW20.CoefficientHolderFiniteness
public import GlobalPhi43.MW20.ScalarSupNorm
public import GlobalPhi43.MW20.PastBallNormDomains

/-!
# MW20 (4.3) from reconstruction and actual parent tree budgets
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set
open scoped ContDiff

/-- The second-product row. Every local norm is its actual value and
is proved finite from the standing smooth fields. All four tree budgets
are at the same parent P_r, with their original counterterms and J/V fields. -/
theorem mw20_row_4_3
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (v J Y Z V : ParabolicSpace → ℝ) (C₂ : ℝ)
    (hv : ContDiff ℝ ∞ v) (hJ : ContDiff ℝ ∞ J) (hY : ContDiff ℝ ∞ Y)
    (hZ : ContDiff ℝ ∞ Z) (hV : ContDiff ℝ ∞ V)
    {r T ε c : ℝ} (hr : 0 ≤ r) (hT : 0 < T) (hT1 : T < 1)
    (hε : 0 < ε) (hsmall : ε < 1 / 14) (hc : 0 ≤ c)
    (x : ParabolicSpace) (hball : Local.pastBall x T ⊆ sourceCylinder r)
    (hbudgetA : recenteredASeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε Y V C₂ ≤
      ENNReal.ofReal (c * sourceSup v r ^ (2 - 4 * ε)))
    (hbudgetV : negativeTreeSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) (-1 - 2 * ε) V ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 - 2 * ε)))
    (hbudgetX : recenteredXVSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε V ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 - 2 * ε)))
    (hbudgetD : recenteredDSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε Z V J C₂ ≤
      ENNReal.ofReal (c * sourceSup v r ^ (5 / 2 - 5 * ε))) :
    let B := Local.pastBall x T
    let M := sourceSup v r
    let Hv := (scalarHolderSeminorm v B (1 / 2 - 3 * ε)).toReal
    let HU := (localAffineSeminorm (sourceExpansion v Y Z) B (3 / 2 - 5 * ε)).toReal
    let Hν := (localCoefficientHolderSeminorm (sourceAffineCoefficient v Y Z) B (1 / 2 - 5 * ε)).toReal
    let N := (localScalarSup (fun a => ‖sourceAffineCoefficient v Y Z a‖) B).toReal
    let μ := infiniteKernelMeasure Φ hΦ T hT
    |pastSmooth μ (fun y => (v y - v x) * V y) x +
      3 * C₂ * (pastSmooth μ v x + pastSmooth μ J x)| ≤ secondProductConstant ε * c *
      (T ^ (1 / 2 - 7 * ε) *
        (Hv * M ^ (2 - 4 * ε) + (HU + Hν) * M ^ (1 - 2 * ε)) +
        M ^ (5 / 2 - 5 * ε) * T ^ (-(1 / 2) - 5 * ε) +
        T ^ (-4 * ε) * M ^ (3 - 4 * ε) + N * M ^ (1 - 2 * ε) * T ^ (-2 * ε)) := by
  let B := Local.pastBall x T
  let M := sourceSup v r
  let Hv := (scalarHolderSeminorm v B (1 / 2 - 3 * ε)).toReal
  let HU := (localAffineSeminorm (sourceExpansion v Y Z) B (3 / 2 - 5 * ε)).toReal
  let Hν := (localCoefficientHolderSeminorm (sourceAffineCoefficient v Y Z) B (1 / 2 - 5 * ε)).toReal
  let N := (localScalarSup (fun a => ‖sourceAffineCoefficient v Y Z a‖) B).toReal
  let R := ‖x‖ + max (T ^ 2) T
  have hDB : B ⊆ Metric.closedBall 0 R := pastBall_subset_compact_ball x hT.le
  have hM : 0 ≤ M := sourceSup_nonneg_of_continuousOn_all hv.continuous.continuousOn hr
  have hHv : 0 ≤ Hv := ENNReal.toReal_nonneg
  have hHU : 0 ≤ HU := ENNReal.toReal_nonneg
  have hHν : 0 ≤ Hν := ENNReal.toReal_nonneg
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  have hnHv := scalarHolderSeminorm_ne_top v hv B R hDB
    (by linarith : 0 ≤ 1 / 2 - 3 * ε) (by linarith : 1 / 2 - 3 * ε ≤ 1)
  have hnU := localAffineSeminorm_ne_top_of_smooth (sourceExpansion v Y Z)
    (sourceExpansion_contDiff v Y Z hv hY hZ) B R hDB
    (by linarith : 0 ≤ 3 / 2 - 5 * ε) (by linarith : 3 / 2 - 5 * ε ≤ 2)
    (fun a _ => Local.expansion_diag v Y Z a)
  have hnν := sourceAffineCoefficient_holder_ne_top v Y Z hv hY hZ B R hDB
    (by linarith : 0 ≤ 1 / 2 - 5 * ε) (by linarith : 1 / 2 - 5 * ε ≤ 1)
  have hνc := (sourceAffineCoefficient_contDiff v Y Z hv hY hZ).continuous
  have hnN := localScalarSup_ne_top (fun a => ‖sourceAffineCoefficient v Y Z a‖) hνc.norm
    B (Metric.closedBall 0 R) hDB (isCompact_closedBall _ _)
  have hbound (Q : ENNReal) (hn : Q ≠ ⊤) : Q ≤ ENNReal.ofReal Q.toReal := by
    rw [ENNReal.ofReal_toReal hn]
  have hAnorm := (recenteredASeminorm_testingKernel_le_sourceKernel Φ hΦ hball ε Y V C₂).trans hbudgetA
  have hVnorm := (negativeTreeSeminorm_testingKernel_le_sourceKernel Φ hΦ hball (-1 - 2 * ε) V).trans hbudgetV
  have hXnorm := (recenteredXVSeminorm_testingKernel_le_sourceKernel Φ hΦ hball ε V).trans hbudgetX
  have hDnorm := (recenteredDSeminorm_testingKernel_le_sourceKernel Φ hΦ hball ε Z V J C₂).trans hbudgetD
  have hsupν : ∀ a ∈ B, ‖sourceAffineCoefficient v Y Z a‖ ≤ N := by
    intro a ha
    simpa only [abs_norm] using localScalarSup_bound (fun a => ‖sourceAffineCoefficient v Y Z a‖)
      B hN (hbound _ hnN) ha
  have hprod := mw20_lemma_2_10_of_norm_bounds Φ hΦ v J Y Z V C₂ hv hJ hY hZ hV x
    hT hT1 hε hsmall hHv hHU hHν (by positivity) (by positivity) (by positivity)
    (hbound _ hnHv) (hbound _ hnU) (hbound _ hnν) hAnorm hVnorm hXnorm hM hN (by positivity)
    (fun a ha => abs_le_sourceSup_of_continuousOn hv.continuous.continuousOn hr (hball ha)) hsupν hDnorm
  simp_rw [← reconstruction_pastSmooth_eq_density Φ hΦ hT hT1.le] at hprod
  rw [second_product_parent_smallness hM hsmall] at hprod
  convert hprod using 1; ring

end GlobalPhi43.MW20
