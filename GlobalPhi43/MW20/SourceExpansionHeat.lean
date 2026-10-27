module

public import GlobalPhi43.MW20.SourceHeatLinear
public import GlobalPhi43.MW20.SourceAffineCoefficient

/-!
# The expansion PDE behind the small-scale row (4.4)
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures
open scoped ContDiff

/-- Smoothness of the actual expansion with its base point fixed. -/
theorem source_expansion_contDiff_right (v Y Z : ParabolicSpace → ℝ)
    (hv : ContDiff ℝ ∞ v) (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z)
    (x : ParabolicSpace) : ContDiff ℝ ∞ (Local.expansion v Y Z x) := by
  have he : Local.expansion v Y Z x = fun y =>
      (v y - v x + Z y - Z x) + 3 * v x * (Y y - Y x) := by
    funext y
    exact Local.expansion_eq v Y Z x y
  rw [he]
  fun_prop

/-- Applying the actual heat operator in the second variable, with all
base-point constants differentiated away and no heat-linearity premise. -/
theorem source_heat_expansion (v Y Z : ParabolicSpace → ℝ)
    (hv : ContDiff ℝ ∞ v) (hY : ContDiff ℝ ∞ Y) (hZ : ContDiff ℝ ∞ Z)
    (x z : ParabolicSpace) :
    sourceHeat (Local.expansion v Y Z x) z =
      sourceHeat v z + sourceHeat Z z + 3 * v x * sourceHeat Y z := by
  have he : Local.expansion v Y Z x = fun y =>
      (v y - v x + Z y - Z x) + (3 * v x) * (Y y - Y x) := by
    funext y
    exact Local.expansion_eq v Y Z x y
  rw [he, sourceHeat_add _ _ (by fun_prop) (by fun_prop),
    sourceHeat_sub_const _ (by fun_prop),
    sourceHeat_add _ _ (by fun_prop) hZ,
    sourceHeat_sub_const v hv, sourceHeat_const_mul _ _ (by fun_prop),
    sourceHeat_sub_const Y hY]

end GlobalPhi43.MW20
