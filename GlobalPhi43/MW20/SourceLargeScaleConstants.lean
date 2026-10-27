module

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
public import GlobalPhi43.MW20.ParentHolderNorm
public import GlobalPhi43.MW20.ParentExpansionIncrement
public import GlobalPhi43.MW20.RadiusAffineSeminorm
public import GlobalPhi43.MW20.LocalSourceHolder
public import Mathlib.Basic.ENNReal.Real
public import GlobalPhi43.MW20.SourceConeEstimate
public import GlobalPhi43.MW20.RadiusCoefficientSup
public import GlobalPhi43.MW20.SourceAffineCoefficient
public import GlobalPhi43.Local.SchauderInputs
public import GlobalPhi43.MW20.ScalarHolderSeminorm
public import GlobalPhi43.MW20.ParentInterpolationAlgebra
public import GlobalPhi43.MW20.ParentHolderCutoff
public import GlobalPhi43.MW20.QuarterWeightTransfer
public import GlobalPhi43.MW20.SourceHolderBridges
public import GlobalPhi43.MW20.SourceQuarterCoefficient
public import GlobalPhi43.MW20.ParentCoefficientAlgebra
public import GlobalPhi43.MW20.ParentCoefficientWeight
public import GlobalPhi43.MW20.CoefficientNormBridges
public import GlobalPhi43.MW20.SourceRadiusWeightedFiniteness
public import GlobalPhi43.MW20.FirstForcingEnvelope
public import GlobalPhi43.MW20.ReciprocalSourceGeometry
public import GlobalPhi43.MW20.SourceSecondProductFullDomain
public import GlobalPhi43.MW20.FullAffineFromRadiusFar
public import GlobalPhi43.MW20.FarAffineScaleAlgebra
public import GlobalPhi43.MW20.AffineTestingDomains
public import GlobalPhi43.MW20.CylinderCoefficientBounds
public import GlobalPhi43.MW20.SecondProductSmallnessAlgebra
public import GlobalPhi43.MW20.CoefficientHolderFiniteness
public import GlobalPhi43.MW20.ScalarSupNorm
public import GlobalPhi43.MW20.SourceCompleteForcing
public import GlobalPhi43.MW20.SecondForcingEnvelope

/-! Source-independent constants for the large-scale assembly. -/

public section

namespace GlobalPhi43.MW20

@[expose] noncomputable def sourceFirstForcingConstant (ε A : ℝ) : ℝ :=
  let C := 312 * (4 ^ ((3 / 2 : ℝ) - 5 * ε) * A + 1)
  (2 * firstProductConstant ε) *
    (C * (2 : ℝ) ^ (1 - 2 * ε) + C * (2 : ℝ) ^ (1 / 2 - 3 * ε) + 3)

@[expose] noncomputable def sourceSecondForcingConstant (ε A : ℝ) : ℝ :=
  let γ := (3 / 2 : ℝ) - 5 * ε
  let P := (4 : ℝ) ^ γ * A + 1
  let Cγ := 200 * ((2 : ℝ) ^ γ + 4) * (1 + (2 : ℝ) ^ γ)
  secondProductConstant ε *
    ((312 * P) * (2 : ℝ) ^ (1 / 2 - 3 * ε) +
      (A + 6 + 216 * P) * (2 : ℝ) ^ γ +
      (4 ^ γ * (5 * Cγ) * P) * (2 : ℝ) ^ γ + 2 + 2 * (72 * P)) + 1

@[expose] noncomputable def sourcePositiveErrorConstant (ε A : ℝ) : ℝ :=
  312 * (4 ^ ((3 / 2 : ℝ) - 5 * ε) * A + 1) * (2 : ℝ) ^ (1 / 2 - 3 * ε)

@[expose] noncomputable def sourceLargeScaleConstant (ε A : ℝ) : ℝ :=
  62 * (1 + sourcePositiveErrorConstant ε A + sourcePositiveErrorConstant ε A ^ (1 / 3 : ℝ) +
    sourceFirstForcingConstant ε A ^ (1 / 3 : ℝ) +
    sourceSecondForcingConstant ε A ^ (1 / 3 : ℝ) + 1)

theorem sourceFirstForcingConstant_nonneg {ε A : ℝ} (hsmall : ε < 1 / 14) (hA : 0 ≤ A) :
    0 ≤ sourceFirstForcingConstant ε A := by
  have hK := (firstProductConstant_pos hsmall).le
  unfold sourceFirstForcingConstant
  positivity

theorem sourceSecondForcingConstant_nonneg {ε A : ℝ} (hsmall : ε < 1 / 14) (hA : 0 ≤ A) :
    0 ≤ sourceSecondForcingConstant ε A := by
  have hK := (secondProductConstant_pos hsmall).le
  unfold sourceSecondForcingConstant
  positivity

theorem sourcePositiveErrorConstant_nonneg {ε A : ℝ} (hA : 0 ≤ A) :
    0 ≤ sourcePositiveErrorConstant ε A := by
  unfold sourcePositiveErrorConstant
  positivity

theorem sourceLargeScaleConstant_nonneg {ε A : ℝ} (hsmall : ε < 1 / 14) (hA : 0 ≤ A) :
    0 ≤ sourceLargeScaleConstant ε A := by
  have hF := sourceFirstForcingConstant_nonneg hsmall hA
  have hG := sourceSecondForcingConstant_nonneg hsmall hA
  have hP := sourcePositiveErrorConstant_nonneg (ε := ε) hA
  unfold sourceLargeScaleConstant
  positivity

end GlobalPhi43.MW20
