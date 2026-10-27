module


public import GlobalPhi43.MW20.SourceSecondProductFullDomain
public import GlobalPhi43.MW20.ClosingCommonInterpolation
public import GlobalPhi43.MW20.ClosingFullAffine
public import GlobalPhi43.MW20.AffineTestingDomains
public import GlobalPhi43.MW20.ScalarTestingDomains
public import GlobalPhi43.MW20.PastBallNormGeometry
public import GlobalPhi43.MW20.CylinderCoefficientBounds
public import GlobalPhi43.MW20.SecondProductSmallnessAlgebra
public import GlobalPhi43.MW20.SourceAffineFiniteness
public import GlobalPhi43.MW20.CoefficientHolderFiniteness
public import GlobalPhi43.MW20.ScalarSupNorm
public import GlobalPhi43.MW20.PastBallNormDomains
public import GlobalPhi43.MW20.FullNormDomains
public import GlobalPhi43.MW20.LocalHolderFiniteness

/-!
# The second product on full affine norms and cutoff 2T
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set
open scoped ContDiff

/-- Actual second forcing from the exact-d0 parent radius budget,
including the separately paid full affine norm and complete counterterm. -/
theorem source_second_forcing_from_radius_bound_positive
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (v J Y Z V : ParabolicSpace → ℝ) (C₂ : ℝ)
    (hv : ContDiff ℝ ∞ v) (hJ : ContDiff ℝ ∞ J) (hY : ContDiff ℝ ∞ Y)
    (hZ : ContDiff ℝ ∞ Z) (hV : ContDiff ℝ ∞ V)
    {r d₀ d T ε c A : ℝ} (hr : 0 ≤ r) (hr1 : r < 1 / 2)
    (hd : d ∈ Ioc (0 : ℝ) d₀) (hT : 0 < T) (hT1 : T < 1)
    (hε : 0 < ε) (hsmall : ε < 1 / 14) (hc : 0 ≤ c)
    (hA : 0 ≤ A) (hMpos : 0 < sourceSup v r) (hscale : d₀ * sourceSup v r ≤ 1)
    (hne : (Local.cylinderInterior r d).Nonempty)
    (hnorm : Local.weightedRadiusAffineSeminorm (sourceExpansion v Y Z) r d₀ ((3 / 2 : ℝ) - 5 * ε) ≤
      ENNReal.ofReal (A * sourceSup v r))
    (hbudgetY : parabolicHolderSeminorm (1 - 2 * ε) (parabolicClosedNbhd mwCylinder 1) Y ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 - 2 * ε)))
    (hbudgetZ : parabolicHolderSeminorm (1 / 2 - 3 * ε) (parabolicClosedNbhd mwCylinder 1) Z ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 + (1 / 2 - 3 * ε))))
    (hc1 : c ≤ 1)
    {x : ParabolicSpace}
    (hball : Local.pastBall x T ⊆ Local.cylinderInterior r d)
    (hbudgetA : recenteredASeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε Y V C₂ ≤
      ENNReal.ofReal (c * sourceSup v r ^ (2 - 4 * ε)))
    (hbudgetV : negativeTreeSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) (-1 - 2 * ε) V ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 - 2 * ε)))
    (hbudgetX : recenteredXVSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε V ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 - 2 * ε)))
    (hbudgetD : recenteredDSeminorm (sourceKernelFamily Φ hΦ) (sourceCylinder r) ε Z V J C₂ ≤
      ENNReal.ofReal (c * sourceSup v r ^ (5 / 2 - 5 * ε))) :
    let M := sourceSup v r
    let γ := (3 / 2 : ℝ) - 5 * ε
    let P := 4 ^ γ * A + 1
    let Cγ := 200 * (2 ^ γ + 4) * (1 + 2 ^ γ)
    let Hv := (312 * P) * M / d ^ (1 / 2 - 3 * ε)
    let HU := (A + 6 + 216 * P) * M / d ^ γ
    let Hν := (4 ^ γ * (5 * Cγ) * P) * M / d ^ γ
    let N := (72 * P) * M / d
    let μ := infiniteKernelMeasure Φ hΦ T hT
    |pastSmooth μ (fun y => (v y - v x) * V y) x +
      3 * C₂ * (pastSmooth μ v x + pastSmooth μ J x)| ≤ secondProductConstant ε * c *
      (T ^ (1 / 2 - 7 * ε) *
        (Hv * M ^ (2 - 4 * ε) + (HU + Hν) * M ^ (1 - 2 * ε)) +
        M ^ (5 / 2 - 5 * ε) * T ^ (-(1 / 2) - 5 * ε) +
        T ^ (-4 * ε) * M ^ (3 - 4 * ε) + N * M ^ (1 - 2 * ε) * T ^ (-2 * ε)) := by
  let γ := (3 / 2 : ℝ) - 5 * ε
  let P := (4 : ℝ) ^ γ * A + 1
  let Cγ := 200 * ((2 : ℝ) ^ γ + 4) * (1 + (2 : ℝ) ^ γ)
  let M := sourceSup v r
  let D := Local.cylinderInterior r d
  have hs := source_common_interpolation_from_radius_bound_positive v Y Z hv hY hZ (2 * T)
    hr hr1 hd hε hsmall hc hc1 hA hne hbudgetY hbudgetZ hMpos hscale hnorm
  have hu := source_full_affine_from_radius_bound_positive v Y Z hv hY hZ hr hr1 hd
    hε hsmall hc hc1 hA hne hbudgetY hbudgetZ hMpos hscale hnorm
  have hp : 0 ≤ P := by dsimp [P]; positivity
  have hM : 0 ≤ M := hMpos.le
  have hCγ : 0 ≤ Cγ := by dsimp [Cγ]; positivity
  have hUr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hu
  have hνr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hs.2.2.2
  change ENNReal.ofReal (d ^ γ) * _ ≤ ENNReal.ofReal ((A + 6 + 216 * P) * M) at hu
  change (ENNReal.ofReal (d ^ γ) * _).toReal ≤
    (ENNReal.ofReal ((A + 6 + 216 * P) * M)).toReal at hUr
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hd.1.le γ),
    ENNReal.toReal_ofReal (by positivity)] at hUr
  change (ENNReal.ofReal (d ^ γ) * _).toReal ≤
    (ENNReal.ofReal (((4 : ℝ) ^ γ * (5 * Cγ) * P) * M)).toReal at hνr
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hd.1.le γ),
    ENNReal.toReal_ofReal (by positivity)] at hνr
  have hHv : localSourceHolder v (1 / 2 - 3 * ε) D (2 * T) ≤
      (312 * P) * M / d ^ (1 / 2 - 3 * ε) :=
    (le_div_iff₀ (Real.rpow_pos_of_pos hd.1 _)).2 (by
      simpa only [D, P, M, γ, Cγ, mul_comm] using hs.2.2.1)
  have hHU : (localAffineSeminorm (sourceExpansion v Y Z) D γ).toReal ≤
      (A + 6 + 216 * P) * M / d ^ γ :=
    (le_div_iff₀ (Real.rpow_pos_of_pos hd.1 γ)).2 (by simpa only [D, P, M, γ, Cγ, mul_comm] using hUr)
  have hHν : (localCoefficientHolderSeminorm (sourceAffineCoefficient v Y Z) D
      (1 / 2 - 5 * ε)).toReal ≤ ((4 : ℝ) ^ γ * (5 * Cγ) * P) * M / d ^ γ :=
    (le_div_iff₀ (Real.rpow_pos_of_pos hd.1 γ)).2 (by simpa only [D, P, M, γ, Cγ, mul_comm] using hνr)
  have hN : (localScalarSup (fun x => ‖sourceAffineCoefficient v Y Z x‖) D).toReal ≤
      (72 * P) * M / d :=
    (le_div_iff₀ hd.1).2 (by simpa only [D, P, M, γ, Cγ, mul_comm] using hs.1)
  have hprod := source_second_product_full_domain Φ hΦ v J Y Z V C₂ hv hJ hY hZ hV
    hr hd.1 hT hT1 hε hsmall hc hball hbudgetA hbudgetV hbudgetX hbudgetD
  have hK := (secondProductConstant_pos hsmall).le
  dsimp only
  apply hprod.trans
  gcongr

end GlobalPhi43.MW20
