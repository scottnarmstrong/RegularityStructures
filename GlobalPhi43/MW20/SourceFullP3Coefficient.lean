module

public import GlobalPhi43.MW20.LocalSourcePairNorms
public import GlobalPhi43.MW20.LocalSourceHolder
public import Mathlib.Basic.ENNReal.Real
public import GlobalPhi43.MW20.SourceConeEstimate
public import GlobalPhi43.MW20.ParentHolderNorm
public import GlobalPhi43.MW20.ParentExpansionIncrement
public import GlobalPhi43.MW20.RadiusAffineSeminorm
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
public import GlobalPhi43.MW20.ReciprocalScaleMonomial
public import GlobalPhi43.MW20.SourceRadiusWeightedFiniteness
public import GlobalPhi43.MW20.SourceSchauderExponents
public import GlobalPhi43.Local.TimeFreeGeometry

/-! The full three-point allowance used by the radius-local expansion estimates. -/

public noncomputable section
namespace GlobalPhi43.MW20
open RegularityStructures Local Set
open scoped ContDiff ENNReal

@[expose] def sourceFullThreePointAllowance (v Y Z : ParabolicSpace → ℝ)
    (ε r d₀ c : ℝ) : ℝ :=
  let γ := (3 / 2 : ℝ) - 5 * ε
  936 * c * (4 ^ γ + 1) *
    ((weightedRadiusAffineSeminorm (sourceExpansion v Y Z) r d₀ γ).toReal + sourceSup v r)

end GlobalPhi43.MW20
