module


public import GlobalPhi43.MW20.ClosingFirstProduct
public import GlobalPhi43.MW20.ClosingCommonInterpolation
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

/-- Actual first forcing from the parent interpolation bound at the
identical radius cutoff d0. All smoothing and Hölder norms are evaluated on the specified domains. -/
theorem source_first_forcing_from_radius_bound_positive
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (v Y Z J : ParabolicSpace → ℝ) (hv : ContDiff ℝ ∞ v)
    (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z) (hJ : ContDiff ℝ ∞ J)
    {r d₀ d T ε c A : ℝ} (hr : 0 ≤ r) (hr1 : r < 1 / 2)
    (hd : d ∈ Ioc (0 : ℝ) d₀) (hT : 0 < T) (hT1 : T < 1)
    (hε : 0 < ε) (hsmall : ε < 1 / 14) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hA : 0 ≤ A) (hMpos : 0 < sourceSup v r) (hscale : d₀ * sourceSup v r ≤ 1)
    (hne : (Local.cylinderInterior r d).Nonempty)
    (hnorm : Local.weightedRadiusAffineSeminorm (sourceExpansion v Y Z) r d₀ ((3 / 2 : ℝ) - 5 * ε) ≤
      ENNReal.ofReal (A * sourceSup v r))
    (hbudgetY : parabolicHolderSeminorm (1 - 2 * ε) (parabolicClosedNbhd mwCylinder 1) Y ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 - 2 * ε)))
    {x : ParabolicSpace}
    (hball : Local.pastBall x T ⊆ Local.cylinderInterior r d)
    (hbudgetZ : parabolicHolderSeminorm (1 / 2 - 3 * ε) (parabolicClosedNbhd mwCylinder 1) Z ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 + (1 / 2 - 3 * ε))))
    (hbudgetJ : negativeTreeSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r)
      (-(1 / 2) - ε) J ≤ ENNReal.ofReal (c * sourceSup v r ^ (1 / 2 - ε)))
    (hbudgetB : recenteredBSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε Z J ≤
      ENNReal.ofReal (c * sourceSup v r ^ (2 - 4 * ε))) :
    let M := sourceSup v r
    let C := 312 * (4 ^ ((3 / 2 : ℝ) - 5 * ε) * A + 1)
    let H := C * M / d ^ (1 - 2 * ε)
    let Hv := C * M / d ^ (1 / 2 - 3 * ε)
    |pastSmooth (infiniteKernelMeasure Φ hΦ T hT) (fun y => v y ^ 2 * J y) x| ≤
      (2 * firstProductConstant ε) * c *
        (T ^ (1 / 2 - 3 * ε) * M ^ (3 / 2 - ε) * H +
          T ^ (1 / 2 - 7 * ε) * M ^ (2 - 4 * ε) * Hv +
          T ^ (-(1 / 2) - ε) * M ^ (5 / 2 - ε) + T ^ (-4 * ε) * M ^ (3 - 4 * ε) +
          T ^ (1 / 2 - 7 * ε) * M ^ (7 / 2 - 7 * ε)) := by
  have hs := source_common_interpolation_from_radius_bound_positive v Y Z hv hY hZ (2 * T)
    hr hr1 hd hε hsmall hc hc1 hA hne hbudgetY hbudgetZ hMpos hscale hnorm
  dsimp only at hs ⊢
  have hH : localSourceHolder (fun y => v y + Z y) (1 - 2 * ε)
      (Local.cylinderInterior r d) (2 * T) ≤
      (312 * (4 ^ ((3 / 2 : ℝ) - 5 * ε) * A + 1)) * sourceSup v r / d ^ (1 - 2 * ε) := (le_div_iff₀ (Real.rpow_pos_of_pos hd.1 (1 - 2 * ε))).2
    (by simpa only [mul_comm] using hs.2.1)
  have hHv : localSourceHolder v (1 / 2 - 3 * ε)
      (Local.cylinderInterior r d) (2 * T) ≤
      (312 * (4 ^ ((3 / 2 : ℝ) - 5 * ε) * A + 1)) * sourceSup v r / d ^ (1 / 2 - 3 * ε) := (le_div_iff₀ (Real.rpow_pos_of_pos hd.1 (1 / 2 - 3 * ε))).2
    (by simpa only [mul_comm] using hs.2.2.1)
  have hprod := source_first_product_full_domain_positive Φ hΦ v Z J hv hZ hJ hr hd.1 hT hT1
    hε.le hsmall hc hc1 hball hbudgetZ hbudgetJ hbudgetB
  have hM := hMpos.le
  have hK := (firstProductConstant_pos hsmall).le
  apply hprod.trans
  gcongr

end GlobalPhi43.MW20
