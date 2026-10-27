module

public import GlobalPhi43.MW20.LocalPositiveHolder
public import GlobalPhi43.MW20.KernelFirstProduct
public import GlobalPhi43.MW20.ScalarHolderFiniteness
public import GlobalPhi43.MW20.PastBallNormDomains
public import GlobalPhi43.MW20.KernelSourceNormBridges
public import GlobalPhi43.MW20.FirstProductSmallnessAlgebra
public import GlobalPhi43.MW20.LocalSourcePairNorms
public import GlobalPhi43.MW20.ScalarTestingDomains
public import GlobalPhi43.MW20.PastBallNormGeometry

/-! First-product estimate from reconstruction and the local positive-tree norm. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set
open scoped ContDiff

theorem mw20_row_4_2_positive
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (v Z J : ParabolicSpace → ℝ) (hv : ContDiff ℝ ∞ v)
    (hZ : ContDiff ℝ ∞ Z) (hJ : ContDiff ℝ ∞ J)
    {r T ε c : ℝ} (hr : 0 ≤ r) (hT : 0 < T) (hT1 : T < 1)
    (hε : 0 ≤ ε) (hsmall : ε < 1 / 14) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (x : ParabolicSpace) (hball : Local.pastBall x T ⊆ sourceCylinder r)
    (hbudgetZ : parabolicHolderSeminorm (1 / 2 - 3 * ε) (parabolicClosedNbhd mwCylinder 1) Z ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 + (1 / 2 - 3 * ε))))
    (hbudgetJ : negativeTreeSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r)
      (-(1 / 2) - ε) J ≤ ENNReal.ofReal (c * sourceSup v r ^ (1 / 2 - ε)))
    (hbudgetB : recenteredBSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε Z J ≤
      ENNReal.ofReal (c * sourceSup v r ^ (2 - 4 * ε))) :
    let B := Local.pastBall x T
    let M := sourceSup v r
    let H := (scalarHolderSeminorm (fun y => v y + Z y) B (1 - 2 * ε)).toReal
    let Hv := (scalarHolderSeminorm v B (1 / 2 - 3 * ε)).toReal
    |pastSmooth (infiniteKernelMeasure Φ hΦ T hT) (fun y => v y ^ 2 * J y) x| ≤
      (2 * firstProductConstant ε) * c *
        (T ^ (1 / 2 - 3 * ε) * M ^ (3 / 2 - ε) * H +
          T ^ (1 / 2 - 7 * ε) * M ^ (2 - 4 * ε) * Hv +
          T ^ (-(1 / 2) - ε) * M ^ (5 / 2 - ε) + T ^ (-4 * ε) * M ^ (3 - 4 * ε) +
          T ^ (1 / 2 - 7 * ε) * M ^ (7 / 2 - 7 * ε)) := by
  let B := Local.pastBall x T
  let M := sourceSup v r
  let H := (scalarHolderSeminorm (fun y => v y + Z y) B (1 - 2 * ε)).toReal
  let Hv := (scalarHolderSeminorm v B (1 / 2 - 3 * ε)).toReal
  have hM : 0 ≤ M := sourceSup_nonneg_of_continuousOn_all hv.continuous.continuousOn hr
  have hH : 0 ≤ H := ENNReal.toReal_nonneg
  have hHv : 0 ≤ Hv := ENNReal.toReal_nonneg
  have hDB := pastBall_subset_compact_ball x hT.le
  have hnH := scalarHolderSeminorm_ne_top (fun y => v y + Z y) (hv.add hZ) B _ hDB
    (by linarith : 0 ≤ 1 - 2 * ε) (by linarith : 1 - 2 * ε ≤ 1)
  have hnHv := scalarHolderSeminorm_ne_top v hv B _ hDB
    (by linarith : 0 ≤ 1 / 2 - 3 * ε) (by linarith : 1 / 2 - 3 * ε ≤ 1)
  have hHnorm : scalarHolderSeminorm (fun y => v y + Z y) B (1 - 2 * ε) ≤ ENNReal.ofReal H := by
    dsimp only [H]
    rw [ENNReal.ofReal_toReal hnH]
  have hHvnorm : scalarHolderSeminorm v B (1 / 2 - 3 * ε) ≤ ENNReal.ofReal Hv := by
    dsimp only [Hv]
    rw [ENNReal.ofReal_toReal hnHv]
  have hZnorm := ((scalarHolderSeminorm_mono_domain Z (hball.trans (sourceCylinder_subset_positive hr))
    (1 / 2 - 3 * ε)).trans_eq (scalarHolderSeminorm_eq_parabolicHolderSeminorm Z _ _)).trans hbudgetZ
  have hJnorm := (negativeTreeSeminorm_testingKernel_le_sourceKernel Φ hΦ hball (-(1 / 2) - ε) J).trans hbudgetJ
  have hBnorm := (recenteredBSeminorm_testingKernel_le_sourceKernel Φ hΦ hball ε Z J).trans hbudgetB
  have hprod := mw20_lemma_2_9_of_norm_bounds Φ hΦ v Z J hv hZ hJ x hT hT1 hε hsmall
    hM hH hHv (by positivity) (by positivity) (by positivity)
    (fun y hy => abs_le_sourceSup_of_continuousOn hv.continuous.continuousOn hr (hball hy))
    hHnorm hHvnorm hZnorm hJnorm hBnorm
  rw [← reconstruction_pastSmooth_eq_density Φ hΦ hT hT1.le] at hprod
  have halg := first_product_parent_smallness hT hsmall hM hH hHv hc hc1
  have hK : 0 ≤ firstProductConstant ε := (firstProductConstant_pos hsmall).le
  apply hprod.trans
  have hh := mul_le_mul_of_nonneg_left halg hK
  convert hh using 1; ring


theorem source_first_product_mixed_domain_positive
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (v Z J : ParabolicSpace → ℝ) (hv : ContDiff ℝ ∞ v)
    (hZ : ContDiff ℝ ∞ Z) (hJ : ContDiff ℝ ∞ J)
    {r d T ε c : ℝ} (hr : 0 ≤ r) (hd : 0 < d) (hT : 0 < T) (h2Td : 2 * T ≤ d)
    (hε : 0 ≤ ε) (hsmall : ε < 1 / 14) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    {x : ParabolicSpace} (hx : x ∈ Local.cylinderInterior r d)
    (hball : Local.pastBall x T ⊆ Local.cylinderInterior r d)
    (hbudgetZ : parabolicHolderSeminorm (1 / 2 - 3 * ε) (parabolicClosedNbhd mwCylinder 1) Z ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 + (1 / 2 - 3 * ε))))
    (hbudgetJ : negativeTreeSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r)
      (-(1 / 2) - ε) J ≤ ENNReal.ofReal (c * sourceSup v r ^ (1 / 2 - ε)))
    (hbudgetB : recenteredBSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε Z J ≤
      ENNReal.ofReal (c * sourceSup v r ^ (2 - 4 * ε))) :
    let D := Local.cylinderInterior r d
    let M := sourceSup v r
    let H := localSourceHolder (fun y => v y + Z y) (1 - 2 * ε) D d
    let Hv := localSourceHolder v (1 / 2 - 3 * ε) D d
    |pastSmooth (infiniteKernelMeasure Φ hΦ T hT) (fun y => v y ^ 2 * J y) x| ≤
      (2 * firstProductConstant ε) * c *
        (T ^ (1 / 2 - 3 * ε) * M ^ (3 / 2 - ε) * H +
          T ^ (1 / 2 - 7 * ε) * M ^ (2 - 4 * ε) * Hv +
          T ^ (-(1 / 2) - ε) * M ^ (5 / 2 - ε) + T ^ (-4 * ε) * M ^ (3 - 4 * ε) +
          T ^ (1 / 2 - 7 * ε) * M ^ (7 / 2 - 7 * ε)) := by
  have hd1 := (mixedInterior_depth_lt_one hr hx).le
  have hT1 : T < 1 := by linarith
  have hvreg := sourceCubicRegularity_of_contDiff (hv.of_le (by simp))
  have hsumreg := sourceCubicRegularity_of_contDiff ((hv.add hZ).of_le (by simp))
  have hM := sourceSup_nonneg_of_continuousOn_all hvreg.continuous hr
  have hbv := mixedInteriorHolder_bddAbove hvreg hr hd (show (1 / 2 : ℝ) - 3 * ε ≤ 1 by linarith) hd1
  have hbs := mixedInteriorHolder_bddAbove hsumreg hr hd (show 1 - 2 * ε ≤ 1 by linarith) hd1
  have hdiam : ∀ a ∈ Local.pastBall x T, ∀ b ∈ Local.pastBall x T, Local.pdist a b ≤ d :=
    fun _ ha _ hb => (pastBall_pair_distance ha hb).trans h2Td
  have hHv := scalarHolderSeminorm_toReal_le_local_holder v hball hd1 hbv hdiam
  have hH := scalarHolderSeminorm_toReal_le_local_holder (fun y => v y + Z y) hball hd1 hbs hdiam
  have hprod := mw20_row_4_2_positive Φ hΦ v Z J hv hZ hJ hr hT hT1 hε hsmall hc hc1 x
    (fun a ha => mixedInterior_subset_base hd.le (hball ha)) hbudgetZ hbudgetJ hbudgetB
  have hK := (firstProductConstant_pos hsmall).le
  apply hprod.trans
  gcongr


end GlobalPhi43.MW20
