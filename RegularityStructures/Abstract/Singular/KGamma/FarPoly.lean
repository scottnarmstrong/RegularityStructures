/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.FarScalar
public import RegularityStructures.Abstract.Singular.Local.Weight
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# Singular Schauder: polynomial components for far pairs

For `x, y` in the slab with `W/64 ≤ d ≤ W` (`d = d(y, x)`, `W = ‖x, y‖_P`), the polynomial
components of `𝒦_γ f(y) − Γ_{yx} 𝒦_γ f(x)` are bounded by
`C K₁ C_f d^{γ+2−|k|} W^{α∧η − γ}`, from the sup bounds at `x`, `y` and a `Γ`-bound at level
`γ + 2` ([Hai14, Prop. 6.16]).
-/

public section

open Set

namespace RegularityStructures

/-- For `x, y` with `d(y, x) ≤ W = ‖x, y‖_P`: `W ≤ ‖x‖_P, ‖y‖_P ≤ 2 W`. -/
theorem weight_le_two_mul_min {x y : ParabolicSpace}
    (hd : parabolicSemigroup.scaleDist y x ≤
      min (singularWeight timeZeroDist x) (singularWeight timeZeroDist y)) :
    singularWeight timeZeroDist x ≤ 2 * min (singularWeight timeZeroDist x)
        (singularWeight timeZeroDist y) ∧
      singularWeight timeZeroDist y ≤ 2 * min (singularWeight timeZeroDist x)
        (singularWeight timeZeroDist y) := by
  have h := abs_le.1 (abs_singularWeight_timeZeroDist_sub_le y x)
  have hsd : parabolicSemigroup.scaleDist y x = parabolicNorm (y - x) := rfl
  rw [hsd] at hd
  rcases le_total (singularWeight timeZeroDist x) (singularWeight timeZeroDist y) with hxy | hxy
  · rw [min_eq_left hxy] at hd ⊢
    constructor <;> linarith [h.1, h.2]
  · rw [min_eq_right hxy] at hd ⊢
    constructor <;> linarith [h.1, h.2]

end RegularityStructures

end
