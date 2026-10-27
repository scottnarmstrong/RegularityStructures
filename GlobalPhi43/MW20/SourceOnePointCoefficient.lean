module

public import GlobalPhi43.MW20.OnePointBudgetScale
public import GlobalPhi43.MW20.LocalHolderFiniteness
public import GlobalPhi43.MW20.SourceAffineFiniteness
public import GlobalPhi43.MW20.ScalarSupNorm

/-!
# The actual nonnegative monotone source one-point coefficient
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set
open scoped ContDiff

/-- The actual source coefficient depends on L and the fixed mixed-domain
norms, with no hidden testing scale T or derivative-norm constant. -/
@[expose] noncomputable def sourceOnePointCoefficient
    (v Y Z : ParabolicSpace → ℝ) (ε r d L c : ℝ) : ℝ :=
  let D := Local.cylinderInterior r d
  let M := sourceSup v r
  let H := localSourceHolder (fun a => v a + Z a) (1 - 2 * ε) D d
  let Hv := localSourceHolder v (1 / 2 - 3 * ε) D d
  let HU := (radiusAffineSeminorm (sourceExpansion v Y Z) D (3 / 2 - 5 * ε) d).toReal
  let Hν := (localCoefficientHolderSeminorm (sourceAffineCoefficient v Y Z) D (1 / 2 - 5 * ε)).toReal
  let N := (localScalarSup (fun a => ‖sourceAffineCoefficient v Y Z a‖) D).toReal
  smallScaleForcingConstant ε * sourceOnePointMajorant ε L M H Hv HU Hν N c

/-- The comparison constant is nonnegative before all source data. -/
theorem smallScaleForcingConstant_nonneg {ε : ℝ} (hsmall : ε < 1 / 14) :
    0 ≤ smallScaleForcingConstant ε := by
  have h₁ := (firstProductConstant_pos hsmall).le
  have h₂ := (secondProductConstant_pos hsmall).le
  unfold smallScaleForcingConstant
  positivity


end GlobalPhi43.MW20
