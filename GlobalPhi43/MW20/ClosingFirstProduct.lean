module

public import GlobalPhi43.MW20.LocalPositiveFirstProduct
public import GlobalPhi43.MW20.KernelFirstProduct
public import GlobalPhi43.MW20.ScalarHolderFiniteness
public import GlobalPhi43.MW20.PastBallNormDomains
public import GlobalPhi43.MW20.KernelSourceNormBridges
public import GlobalPhi43.MW20.FirstProductSmallnessAlgebra
public import GlobalPhi43.MW20.LocalSourcePairNorms
public import GlobalPhi43.MW20.ScalarTestingDomains
public import GlobalPhi43.MW20.PastBallNormGeometry
public import GlobalPhi43.MW20.SourceAffineFiniteness
public import GlobalPhi43.MW20.FullNormDomains
public import GlobalPhi43.MW20.LocalHolderFiniteness

/-!
# The first product at its actual testing cutoff
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set
open scoped ContDiff

/-- Actual (4.2) on a containing mixed domain, using cutoff 2T.
No comparison of 2T with the domain depth is imposed. -/
theorem source_first_product_full_domain_positive
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (v Z J : ParabolicSpace → ℝ) (hv : ContDiff ℝ ∞ v)
    (hZ : ContDiff ℝ ∞ Z) (hJ : ContDiff ℝ ∞ J)
    {r d T ε c : ℝ} (hr : 0 ≤ r) (hd : 0 < d) (hT : 0 < T) (hT1 : T < 1)
    (hε : 0 ≤ ε) (hsmall : ε < 1 / 14) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    {x : ParabolicSpace}
    (hball : Local.pastBall x T ⊆ Local.cylinderInterior r d)
    (hbudgetZ : parabolicHolderSeminorm (1 / 2 - 3 * ε) (parabolicClosedNbhd mwCylinder 1) Z ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 + (1 / 2 - 3 * ε))))
    (hbudgetJ : negativeTreeSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r)
      (-(1 / 2) - ε) J ≤ ENNReal.ofReal (c * sourceSup v r ^ (1 / 2 - ε)))
    (hbudgetB : recenteredBSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε Z J ≤
      ENNReal.ofReal (c * sourceSup v r ^ (2 - 4 * ε))) :
    let D := Local.cylinderInterior r d
    let M := sourceSup v r
    let H := localSourceHolder (fun y => v y + Z y) (1 - 2 * ε) D (2 * T)
    let Hv := localSourceHolder v (1 / 2 - 3 * ε) D (2 * T)
    |pastSmooth (infiniteKernelMeasure Φ hΦ T hT) (fun y => v y ^ 2 * J y) x| ≤
      (2 * firstProductConstant ε) * c *
        (T ^ (1 / 2 - 3 * ε) * M ^ (3 / 2 - ε) * H +
          T ^ (1 / 2 - 7 * ε) * M ^ (2 - 4 * ε) * Hv +
          T ^ (-(1 / 2) - ε) * M ^ (5 / 2 - ε) + T ^ (-4 * ε) * M ^ (3 - 4 * ε) +
          T ^ (1 / 2 - 7 * ε) * M ^ (7 / 2 - 7 * ε)) := by
  have hM := sourceSup_nonneg_of_continuousOn_all hv.continuous.continuousOn hr
  have hDb := mixedInterior_subset_unit_closedBall hr hd.le
  have hbv := localSourceHolder_bddAbove_of_smooth v hv _ 1 hDb
    (by linarith : 0 ≤ (1 / 2 : ℝ) - 3 * ε)
    (by linarith : (1 / 2 : ℝ) - 3 * ε ≤ 1) (2 * T)
  have hbs := localSourceHolder_bddAbove_of_smooth (fun y => v y + Z y) (hv.add hZ)
    _ 1 hDb (by linarith : 0 ≤ 1 - 2 * ε) (by linarith : 1 - 2 * ε ≤ 1) (2 * T)
  have hdiam : ∀ a ∈ Local.pastBall x T, ∀ b ∈ Local.pastBall x T,
      Local.pdist a b ≤ 2 * T := fun _ ha _ hb => pastBall_pair_distance ha hb
  have hHv := scalarHolderSeminorm_toReal_le_local_holder_any_cutoff v hball hbv hdiam
  have hH := scalarHolderSeminorm_toReal_le_local_holder_any_cutoff
    (fun y => v y + Z y) hball hbs hdiam
  have hprod := mw20_row_4_2_positive Φ hΦ v Z J hv hZ hJ hr hT hT1 hε hsmall hc hc1 x
    (fun a ha => mixedInterior_subset_base hd.le (hball ha)) hbudgetZ hbudgetJ hbudgetB
  have hK := (firstProductConstant_pos hsmall).le
  apply hprod.trans
  gcongr

end GlobalPhi43.MW20
