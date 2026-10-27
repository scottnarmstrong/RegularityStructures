module


public import GlobalPhi43.MW20.ClosingHolderError
public import GlobalPhi43.MW20.CommutatorParentError

/-! The actual large-scale source cubic commutator from parent bounds. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set
open scoped ContDiff

/-- The c-free cubic commutator error in (4.31), with parent amplitude
and k^(-1/6+epsilon). Every Holder and amplitude norm is its actual value. -/
theorem source_commutator_parent_error_positive
    (v Y Z : ParabolicSpace → ℝ)
    (hv : ContDiff ℝ ∞ v) (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z)
    {r k ε c A : ℝ} (hr : 0 ≤ r) (hk : 2 < k)
    (hε : 0 < ε) (hsmall : ε < 1 / 14) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hA : 0 ≤ A) (hMpos : 0 < sourceSup v r)
    (hS : r + 1 / sourceSup v r ≤ 1 / 2)
    (hnorm : Local.weightedRadiusAffineSeminorm (sourceExpansion v Y Z)
      r (1 / sourceSup v r) ((3 / 2 : ℝ) - 5 * ε) ≤ ENNReal.ofReal (A * sourceSup v r))
    (hbudgetY : parabolicHolderSeminorm (1 - 2 * ε) (parabolicClosedNbhd mwCylinder 1) Y ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 - 2 * ε)))
    (hbudgetZ : parabolicHolderSeminorm (1 / 2 - 3 * ε) (parabolicClosedNbhd mwCylinder 1) Z ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 + (1 / 2 - 3 * ε)))) :
    let M := sourceSup v r
    let T := (1 / M) / k
    let d := (1 / M) * (k - 1) / k
    let α := (1 / 2 : ℝ) - 3 * ε
    let C := 312 * (4 ^ ((3 / 2 : ℝ) - 5 * ε) * A + 1) * (2 : ℝ) ^ α
    cubicCommutatorScale (sourceSup v (r + d))
      (sourceHolder v α (r + d) (2 * T)) T α ≤
      C ^ (1 / 3 : ℝ) * M * k ^ (-α / 3) := by
  let M := sourceSup v r
  let T := (1 / M) / k
  let d := (1 / M) * (k - 1) / k
  let α := (1 / 2 : ℝ) - 3 * ε
  have hg := reciprocal_source_geometry hr hMpos hk hS
  dsimp only at hg
  have hd : 0 < d := hg.2.2.1.1
  have hR : r + d ∈ Icc (0 : ℝ) (1 / 2) :=
    ⟨by positivity, by dsimp [d]; linarith [hg.2.2.1.2]⟩
  have hm := sourceSup_nonneg hv.continuous hR
  have hmM := sourceSup_antitone hv.continuous ⟨hr, hg.2.2.2.2.1.le⟩ hR
    (le_add_of_nonneg_right hd.le)
  have hb := localSourceHolder_bddAbove_of_smooth v hv (sourceCylinder (r + d)) 1
    ((sourceCylinder_add_subset_mixed hr hd.le).trans
      (mixedInterior_subset_unit_closedBall hr hd.le))
    (by dsimp [α]; linarith : 0 ≤ α) (by dsimp [α]; linarith : α ≤ 1) (2 * T)
  have hH : 0 ≤ sourceHolder v α (r + d) (2 * T) := sourceHolder_nonneg hb
  have he := source_holder_testing_error_positive v Y Z hv hY hZ hr hk hε hsmall hc hc1 hA hMpos hS
    (le_rfl : r + (1 / sourceSup v r) * (k - 1) / k ≤ r + (1 / sourceSup v r) * (k - 1) / k)
    hnorm hbudgetY hbudgetZ
  dsimp only
  exact commutator_scale_from_parent_error hm hMpos hmM hH hg.1.le
    (by linarith : 0 < k) (by positivity) he

end GlobalPhi43.MW20
