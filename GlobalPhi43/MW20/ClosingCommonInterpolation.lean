module

public import GlobalPhi43.MW20.LocalPositiveBudgets

public import GlobalPhi43.MW20.ParentHolderNorm
public import GlobalPhi43.MW20.ParentExpansionIncrement
public import GlobalPhi43.MW20.RadiusAffineSeminorm
public import GlobalPhi43.MW20.LocalSourcePairNorms
public import GlobalPhi43.MW20.LocalSourceHolder
public import Mathlib.Basic.ENNReal.Real
public import GlobalPhi43.MW20.SourceConeEstimate
public import GlobalPhi43.MW20.RadiusCoefficientSup
public import GlobalPhi43.MW20.CylinderCoefficientBounds
public import GlobalPhi43.MW20.SourceAffineCoefficient
public import GlobalPhi43.Local.SchauderInputs
public import GlobalPhi43.MW20.ScalarHolderSeminorm
public import GlobalPhi43.MW20.ParentInterpolationAlgebra
public import GlobalPhi43.MW20.ParentHolderCutoff
public import GlobalPhi43.MW20.QuarterWeightTransfer
public import GlobalPhi43.MW20.SourceAffineFiniteness
public import GlobalPhi43.MW20.LocalHolderFiniteness
public import GlobalPhi43.MW20.ScalarSupNorm
public import GlobalPhi43.MW20.SourceHolderBridges
public import GlobalPhi43.MW20.SourceQuarterCoefficient
public import GlobalPhi43.MW20.ParentCoefficientAlgebra
public import GlobalPhi43.MW20.ParentCoefficientWeight
public import GlobalPhi43.MW20.CoefficientNormBridges
public import GlobalPhi43.MW20.SourceRadiusWeightedFiniteness

/-! Parent interpolation rows after the actual radius Schauder bound. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set
open scoped ContDiff

/-- Actual scalar, coefficient-supremum and coefficient Holder budgets
on D_d from the exact-d0 radius bound, at every scalar testing cutoff. -/
theorem source_common_interpolation_from_radius_bound_positive
    (v Y Z : ParabolicSpace → ℝ)
    (hv : ContDiff ℝ ∞ v) (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z)
    {r d₀ d ε c A : ℝ} (L : ℝ) (hr : 0 ≤ r) (hr1 : r < 1 / 2)
    (hd : d ∈ Ioc (0 : ℝ) d₀) (hε : 0 < ε) (hsmall : ε < 1 / 14)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (hA : 0 ≤ A)
    (hne : (Local.cylinderInterior r d).Nonempty)
    (hbudgetY : parabolicHolderSeminorm (1 - 2 * ε) (parabolicClosedNbhd mwCylinder 1) Y ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 - 2 * ε)))
    (hbudgetZ : parabolicHolderSeminorm (1 / 2 - 3 * ε) (parabolicClosedNbhd mwCylinder 1) Z ≤
      ENNReal.ofReal (c * sourceSup v r ^ (1 + (1 / 2 - 3 * ε))))
    (hMpos : 0 < sourceSup v r) (hscale : d₀ * sourceSup v r ≤ 1)
    (hnorm : Local.weightedRadiusAffineSeminorm (sourceExpansion v Y Z) r d₀ ((3 / 2 : ℝ) - 5 * ε) ≤
      ENNReal.ofReal (A * sourceSup v r)) :
    let D := Local.cylinderInterior r d
    let M := sourceSup v r
    let α := (1 / 2 : ℝ) - 3 * ε
    let β := 1 - 2 * ε
    let γ := (3 / 2 : ℝ) - 5 * ε
    let Cγ : ℝ := 200 * (2 ^ γ + 4) * (1 + 2 ^ γ)
    d * (localScalarSup (fun x => ‖sourceAffineCoefficient v Y Z x‖) D).toReal ≤
      (72 * (4 ^ γ * A + 1)) * M ∧
    d ^ β * localSourceHolder (fun x => v x + Z x) β D L ≤
      (312 * (4 ^ γ * A + 1)) * M ∧
    d ^ α * localSourceHolder v α D L ≤ (312 * (4 ^ γ * A + 1)) * M ∧
    ENNReal.ofReal (d ^ γ) * localCoefficientHolderSeminorm (sourceAffineCoefficient v Y Z)
      D (1 / 2 - 5 * ε) ≤ ENNReal.ofReal ((4 ^ γ * (5 * Cγ) * (4 ^ γ * A + 1)) * M) := by
  let γ := (3 / 2 : ℝ) - 5 * ε
  let D := Local.cylinderInterior r (d / 4)
  let H := (radiusAffineSeminorm (sourceExpansion v Y Z) D γ (d / 4)).toReal
  let M := sourceSup v r
  have hγ : 0 ≤ γ := by dsimp [γ]; linarith
  have hγ2 : γ ≤ 2 := by dsimp [γ]; linarith
  have hS := ENNReal.toReal_mono ENNReal.ofReal_ne_top hnorm
  rw [ENNReal.toReal_ofReal (mul_nonneg hA hMpos.le)] at hS
  have hq := source_weightedRadiusAffineSeminorm_quarter_bound v Y Z hv hY hZ hr hγ hγ2 hd
  have hq' := hq.trans (mul_le_mul_of_nonneg_left hS (by positivity))
  have hB : d ^ γ * H + M ≤ ((4 : ℝ) ^ γ * A + 1) * M := by
    dsimp only [H, D, M] at hq' ⊢
    nlinarith only [hq']
  have hscaleD : d * sourceSup v r ≤ 1 :=
    (mul_le_mul_of_nonneg_right hd.2 hMpos.le).trans hscale
  have hs := source_parent_common_scalar_weighted_positive v Y Z hv hY hZ L hr hr1 hd.1
    hε hsmall hc hc1 hne hbudgetY hbudgetZ hMpos hscaleD
  have hν := source_parent_common_coefficient_holder_positive v Y Z hv hY hZ hr hr1 hd.1
    hε hsmall hc hc1 hne hbudgetY hbudgetZ hMpos hscaleD
  have hN := source_parent_common_coefficient_sup_positive v Y Z hv hY hZ hr hr1 hd.1
    hε hsmall hc hc1 hne hbudgetY hbudgetZ hMpos hscaleD
  dsimp only at hs hν hN ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith only [hN, mul_le_mul_of_nonneg_left hB (by norm_num : (0 : ℝ) ≤ 72)]
  · nlinarith only [hs.1, mul_le_mul_of_nonneg_left hB (by norm_num : (0 : ℝ) ≤ 312)]
  · nlinarith only [hs.2, mul_le_mul_of_nonneg_left hB (by norm_num : (0 : ℝ) ≤ 312)]
  · rw [← ENNReal.ofReal_toReal hν.1, ← ENNReal.ofReal_mul (Real.rpow_nonneg hd.1.le _)]
    apply ENNReal.ofReal_le_ofReal
    exact hν.2.trans (by
      convert mul_le_mul_of_nonneg_left hB
        (by positivity : 0 ≤ (4 : ℝ) ^ γ * (5 * (200 * (2 ^ γ + 4) * (1 + 2 ^ γ)))) using 1
      ring)

end GlobalPhi43.MW20
