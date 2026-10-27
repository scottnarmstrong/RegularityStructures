module


public import GlobalPhi43.MW20.ClosingFirstRadius
public import GlobalPhi43.MW20.FirstForcingEnvelope
public import GlobalPhi43.MW20.ReciprocalSourceGeometry

/-! The actual first forcing supremum at T=d0/k. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set
open scoped ContDiff

/-- Actual parent first-product forcing on P_(r+1/M), with uniform
constant depending only on epsilon and the prior radius allowance A. -/
theorem source_first_forcing_sup_positive
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (v Y Z J : ParabolicSpace → ℝ) (hv : ContDiff ℝ ∞ v)
    (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z) (hJ : ContDiff ℝ ∞ J)
    {r k ε c A : ℝ} (hr : 0 ≤ r) (hk : 2 < k)
    (hε : 0 < ε) (hsmall : ε < 1 / 14) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hA : 0 ≤ A) (hMpos : 0 < sourceSup v r)
    (hS : r + 1 / sourceSup v r ≤ 1 / 2)
    (hnorm : Local.weightedRadiusAffineSeminorm (sourceExpansion v Y Z) r (1 / sourceSup v r) ((3 / 2 : ℝ) - 5 * ε) ≤
      ENNReal.ofReal (A * sourceSup v r))
    (hbudgetY : parabolicHolderSeminorm (1 - 2 * ε) (parabolicClosedNbhd mwCylinder 1) Y ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 - 2 * ε)))
    (hbudgetZ : parabolicHolderSeminorm (1 / 2 - 3 * ε) (parabolicClosedNbhd mwCylinder 1) Z ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 + (1 / 2 - 3 * ε))))
    (hbudgetJ : negativeTreeSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r)
      (-(1 / 2) - ε) J ≤ ENNReal.ofReal (c * sourceSup v r ^ (1 / 2 - ε)))
    (hbudgetB : recenteredBSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε Z J ≤
      ENNReal.ofReal (c * sourceSup v r ^ (2 - 4 * ε))) :
    let M := sourceSup v r
    let C := 312 * (4 ^ ((3 / 2 : ℝ) - 5 * ε) * A + 1)
    let K := (2 * firstProductConstant ε) *
      (C * (2 : ℝ) ^ (1 - 2 * ε) + C * (2 : ℝ) ^ (1 / 2 - 3 * ε) + 3)
    let T := (1 / M) / k
    let μ := infiniteKernelMeasure Φ hΦ T
      (div_pos (one_div_pos.mpr hMpos) (by linarith : 0 < k))
    sourceSup (pastSmooth μ (fun y => v y ^ 2 * J y)) (r + 1 / M) ≤
      K * c * M ^ (3 : ℝ) * k ^ (3 / 2 + 3 * ε) := by
  have hg := reciprocal_source_geometry hr hMpos hk hS
  dsimp only at hg ⊢
  have hpos : 0 ≤ 312 * ((4 : ℝ) ^ ((3 / 2 : ℝ) - 5 * ε) * A + 1) := by positivity
  have he := first_forcing_envelope_bound hMpos hk hpos hε hsmall
  dsimp only at he
  have hK := (firstProductConstant_pos hsmall).le
  apply csSup_le ((sourceCylinder_nonempty
    (show r + 1 / sourceSup v r ∈ Icc (0 : ℝ) (1 / 2) from ⟨by positivity, hS⟩)).image _)
  rintro z ⟨x, hx, rfl⟩
  have hball := large_scale_testing_ball_subset hr (one_div_pos.mpr hMpos) hk hx
  have hp := source_first_forcing_from_radius_bound_positive Φ hΦ v Y Z J hv hY hZ hJ
    hr hg.2.2.2.2.1 hg.2.2.1 hg.1 hg.2.1 hε hsmall hc hc1 hA hMpos
    hg.2.2.2.1 hg.2.2.2.2.2 hnorm hbudgetY hball hbudgetZ hbudgetJ hbudgetB
  apply hp.trans
  have hb := mul_le_mul_of_nonneg_left he (show 0 ≤ (2 * firstProductConstant ε) * c by positivity)
  convert hb using 1; ring

end GlobalPhi43.MW20
