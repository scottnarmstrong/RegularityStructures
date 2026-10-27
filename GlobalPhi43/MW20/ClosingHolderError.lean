module


public import GlobalPhi43.MW20.ClosingCommonInterpolation
public import GlobalPhi43.MW20.ReciprocalSourceGeometry
public import GlobalPhi43.MW20.PositiveTestScale

/-! Actual source Holder smoothing errors at T=d0/k. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set
open scoped ContDiff

/-- Parent interpolation pays the actual smoothing error on every source
cylinder contained in the common forcing domain, with no local norm input. -/
theorem source_holder_testing_error_positive
    (v Y Z : ParabolicSpace → ℝ)
    (hv : ContDiff ℝ ∞ v) (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z)
    {r k ε c A R : ℝ} (hr : 0 ≤ r) (hk : 2 < k)
    (hε : 0 < ε) (hsmall : ε < 1 / 14) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hA : 0 ≤ A) (hMpos : 0 < sourceSup v r)
    (hS : r + 1 / sourceSup v r ≤ 1 / 2)
    (hR : r + (1 / sourceSup v r) * (k - 1) / k ≤ R)
    (hnorm : Local.weightedRadiusAffineSeminorm (sourceExpansion v Y Z)
      r (1 / sourceSup v r) ((3 / 2 : ℝ) - 5 * ε) ≤ ENNReal.ofReal (A * sourceSup v r))
    (hbudgetY : parabolicHolderSeminorm (1 - 2 * ε) (parabolicClosedNbhd mwCylinder 1) Y ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 - 2 * ε)))
    (hbudgetZ : parabolicHolderSeminorm (1 / 2 - 3 * ε) (parabolicClosedNbhd mwCylinder 1) Z ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 + (1 / 2 - 3 * ε)))) :
    let M := sourceSup v r
    let T := (1 / M) / k
    let α := (1 / 2 : ℝ) - 3 * ε
    let C := 312 * (4 ^ ((3 / 2 : ℝ) - 5 * ε) * A + 1)
    sourceHolder v α R (2 * T) * T ^ α ≤ C * (2 : ℝ) ^ α * M * k ^ (-α) := by
  let d := (1 / sourceSup v r) * (k - 1) / k
  let T := (1 / sourceSup v r) / k
  let α := (1 / 2 : ℝ) - 3 * ε
  have hg := reciprocal_source_geometry hr hMpos hk hS
  dsimp only at hg
  have hd : 0 < d := hg.2.2.1.1
  have hα : 0 ≤ α := by dsimp [α]; linarith
  have hs := source_common_interpolation_from_radius_bound_positive v Y Z hv hY hZ (2 * T)
    hr hg.2.2.2.2.1 hg.2.2.1 hε hsmall hc hc1 hA hg.2.2.2.2.2
    hbudgetY hbudgetZ hMpos hg.2.2.2.1 hnorm
  have hDE : sourceCylinder R ⊆ Local.cylinderInterior r d :=
    (sourceCylinder_antitone (by positivity : 0 ≤ r + d) hR).trans
      (sourceCylinder_add_subset_mixed hr hd.le)
  have hb := localSourceHolder_bddAbove_of_smooth v hv _ 1
    (mixedInterior_subset_unit_closedBall hr hd.le) hα
    (by dsimp [α]; linarith : α ≤ 1) (2 * T)
  have hm := localSourceHolder_mono_of_bddAbove v α hDE le_rfl hb
  change sourceHolder v α R (2 * T) ≤ localSourceHolder v α (Local.cylinderInterior r d) (2 * T) at hm
  have hweighted := (mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg hd.le α)).trans hs.2.2.1
  dsimp only
  exact parent_holder_testing_error hMpos hk (by positivity) hα hweighted

end GlobalPhi43.MW20
