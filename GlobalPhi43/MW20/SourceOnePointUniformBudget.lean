module

public import GlobalPhi43.MW20.OnePointMajorantWeight
public import GlobalPhi43.MW20.SourceOnePointCoefficient
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
public import GlobalPhi43.MW20.SourceHolderBridges
public import GlobalPhi43.MW20.SourceQuarterCoefficient
public import GlobalPhi43.MW20.ParentCoefficientAlgebra
public import GlobalPhi43.MW20.ParentCoefficientWeight
public import GlobalPhi43.MW20.CoefficientNormBridges
public import GlobalPhi43.MW20.ScalarSupNorm
public import GlobalPhi43.MW20.SourceWeightedAffineFiniteness

/-! Fixed constants and the inner one-point budget. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set
open scoped ContDiff

/-- The one-point weight constant is chosen from epsilon before the data. -/
@[expose] noncomputable def sourceOnePointWeightConstant (ε : ℝ) : ℝ :=
  let γ := (3 / 2 : ℝ) - 5 * ε
  let Cγ : ℝ := 200 * (2 ^ γ + 4) * (1 + 2 ^ γ)
  1 + (1325 + 4 ^ γ * (5 * Cγ)) * (4 ^ γ + 1)

/-- The common scale-independent budget; S is the actual weighted
radius-affine supremum in its source application. -/
@[expose] noncomputable def sourceOnePointUniformBudget (ε M S c : ℝ) : ℝ :=
  smallScaleForcingConstant ε * (M + c * sourceOnePointWeightConstant ε * (S + M))

theorem sourceOnePointWeightConstant_nonneg (ε : ℝ) :
    0 ≤ sourceOnePointWeightConstant ε := by
  unfold sourceOnePointWeightConstant
  positivity

theorem sourceOnePointUniformBudget_nonneg {ε M S c : ℝ}
    (hsmall : ε < 1 / 14) (hM : 0 ≤ M) (hS : 0 ≤ S) (hc : 0 ≤ c) :
    0 ≤ sourceOnePointUniformBudget ε M S c := by
  exact mul_nonneg (smallScaleForcingConstant_nonneg hsmall)
    (add_nonneg hM (mul_nonneg (mul_nonneg hc (sourceOnePointWeightConstant_nonneg ε))
      (add_nonneg hS hM)))

end GlobalPhi43.MW20
