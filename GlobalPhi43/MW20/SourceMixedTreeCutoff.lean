module

public import GlobalPhi43.MW20.SourceKernelTreeTests
public import GlobalPhi43.MW20.LocalHolderFiniteness
public import GlobalPhi43.MW20.SourceAffineFiniteness
public import GlobalPhi43.MW20.MixedInteriorHolder
public import GlobalPhi43.MW20.LocalSourcePairNorms

/-!
# The mixed increment/tree bound [MW20, (4.6)]
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set
open scoped ContDiff

/-- MW20 (4.6), on the actual mixed-time interior, with the actual local
Holder norm and actual negative tree budget. The parent amplitude is retained. -/
theorem source_mixed_tree_cutoff (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    {v V : ParabolicSpace → ℝ} (hv : ContDiff ℝ ∞ v)
    {r d L T ε c M K : ℝ} (hr : 0 ≤ r) (hd : 0 < d) (hK1 : K ≤ 1)
    (hL0 : 0 ≤ L) (hLK : L ≤ K) (hα0 : 0 ≤ (1 / 2 : ℝ) - 3 * ε)
    (hα1 : (1 / 2 : ℝ) - 3 * ε ≤ 1) (hc : 0 ≤ c) (hM : 0 ≤ M)
    (hbudget : negativeTreeSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r)
      (-1 - 2 * ε) V ≤ ENNReal.ofReal (c * M ^ (1 - 2 * ε)))
    {x y : ParabolicSpace} (hx : x ∈ Local.cylinderInterior r d)
    (hy : y ∈ Local.cylinderInterior r d) (hxy : Local.pdist x y ≤ L)
    (hT : 0 < T) (hT1 : T ≤ 1) :
    |(v y - v x) * pastSmooth (infiniteKernelMeasure Φ hΦ T hT) V y| ≤
      L ^ (1 / 2 - 3 * ε) * T ^ (-1 - 2 * ε) * c *
        localSourceHolder v (1 / 2 - 3 * ε) (Local.cylinderInterior r d) K *
          M ^ (1 - 2 * ε) := by
  have hb := localSourceHolder_bddAbove_of_smooth v hv _ 1
    (mixedInterior_subset_unit_closedBall hr hd.le) hα0 hα1 K
  have hH := localSourceHolder_nonneg hb
  have hinc := localSourceHolder_increment hb hx hy (hxy.trans hLK) hK1
  have hinc' : |v y - v x| ≤
      localSourceHolder v (1 / 2 - 3 * ε) (Local.cylinderInterior r d) K *
        L ^ (1 / 2 - 3 * ε) :=
    hinc.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Local.pdist_nonneg x y) hxy hα0) hH)
  have ht := negativeTreeSeminorm_test_bound (sourceKernelFamily Φ hΦ)
    (sourceCylinder r) (-1 - 2 * ε) V
    (mul_nonneg hc (Real.rpow_nonneg hM _)) hbudget
    (mixedInterior_subset_base hd.le hy) hT hT1
  rw [sourceKernelFamily_pos Φ hΦ hT] at ht
  rw [abs_mul]
  calc
    _ ≤ (localSourceHolder v (1 / 2 - 3 * ε) (Local.cylinderInterior r d) K *
        L ^ (1 / 2 - 3 * ε)) * (c * M ^ (1 - 2 * ε) * T ^ (-1 - 2 * ε)) :=
      mul_le_mul hinc' ht (abs_nonneg _) (mul_nonneg hH (Real.rpow_nonneg hL0 _))
    _ = _ := by ring

end GlobalPhi43.MW20
