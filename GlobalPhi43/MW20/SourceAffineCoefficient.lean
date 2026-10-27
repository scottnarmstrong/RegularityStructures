module

public import GlobalPhi43.MW20.AffineSeminorm
public import GlobalPhi43.MW20.SmoothAffineCoefficient
public import GlobalPhi43.Local.Algebra

/-! The optimal coefficient attached to the local expansion [MW20, (2.29)]. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set
open scoped ContDiff

/-- The actual two-variable source expansion, as a function on the product. -/
@[expose] def sourceExpansion (v Y Z : ParabolicSpace → ℝ)
    (p : ParabolicSpace × ParabolicSpace) : ℝ := Local.expansion v Y Z p.1 p.2

/-- Source smoothness supplies smoothness of the actual expansion. -/
theorem sourceExpansion_contDiff (v Y Z : ParabolicSpace → ℝ)
    (hv : ContDiff ℝ ∞ v) (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z) :
    ContDiff ℝ ∞ (sourceExpansion v Y Z) := by
  unfold sourceExpansion
  simp only [Local.expansion_eq]
  fun_prop

/-- The source's optimal ν, selected from the actual expansion (2.29). -/
@[expose] noncomputable def sourceAffineCoefficient (v Y Z : ParabolicSpace → ℝ) :
    ParabolicSpace → Fin 3 → ℝ := diagonalSpatialCoefficient (sourceExpansion v Y Z)

/-- The selected source coefficient is smooth; this supplies the ν premise of
smooth second-product testing directly from the actual fields. -/
theorem sourceAffineCoefficient_contDiff (v Y Z : ParabolicSpace → ℝ)
    (hv : ContDiff ℝ ∞ v) (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z) :
    ContDiff ℝ ∞ (sourceAffineCoefficient v Y Z) :=
  diagonalSpatialCoefficient_contDiff _ (sourceExpansion_contDiff v Y Z hv hY hZ)

end GlobalPhi43.MW20
