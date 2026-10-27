module

public import GlobalPhi43.MW20.SourceExpansionHeat
public import GlobalPhi43.MW20.GlobalHeatSmoothing
public import GlobalPhi43.MW20.PastBallTesting
public import GlobalPhi43.MW20.LocalSourcePairNorms
public import GlobalPhi43.MW20.SourceTestingCube
public import GlobalPhi43.MW20.SourceKernelTreeTests
public import GlobalPhi43.MW20.MixedInteriorHolder
public import GlobalPhi43.MW20.ExpansionForcingAlgebra
public import GlobalPhi43.MW20.KernelFirstProduct
public import GlobalPhi43.MW20.ScalarHolderFiniteness
public import GlobalPhi43.MW20.PastBallNormDomains
public import GlobalPhi43.MW20.KernelSourceNormBridges
public import GlobalPhi43.MW20.FirstProductSmallnessAlgebra
public import GlobalPhi43.MW20.ScalarTestingDomains
public import GlobalPhi43.MW20.PastBallNormGeometry
public import GlobalPhi43.MW20.SourceSecondProductDomain
public import GlobalPhi43.MW20.SmallScaleForcingBudget
public import GlobalPhi43.MW20.OnePointBudgetScale
public import GlobalPhi43.MW20.SourceSchauderExponents
public import GlobalPhi43.MW20.SourceOnePointCoefficient
public import GlobalPhi43.Local.RadiusGeometry
public import GlobalPhi43.Local.PastAffineError

/-! The affine approximation inequality for a heat-smoothed section. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures

/-- The ordinary-heat affine approximation inequality for the smoothed
section. It bounds the error at radius ηL by the error at radius L and
the supremum of the heat operator on the larger ball. -/
@[expose] noncomputable def sourceCaloricStep
    (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (U : ParabolicSpace × ParabolicSpace → ℝ) (C η L : ℝ)
    (hη : 0 < η) (hL : 0 < L) (x : ParabolicSpace) : Prop :=
  let μ := infiniteKernelMeasure Φ hΦ (η ^ 2 * L) (mul_pos (sq_pos_of_pos hη) hL)
  let g := pastSmooth μ (fun y => U (x, y))
  let Qheat := localScalarSup (sourceHeat g) (Local.pastBall x L)
  Local.pastAffineError g x (η * L) ≤
    ENNReal.ofReal (C * ((η * L) / L) ^ 2) * Local.pastAffineError g x L +
      ENNReal.ofReal (C * L ^ 2 * Qheat.toReal)

end GlobalPhi43.MW20
