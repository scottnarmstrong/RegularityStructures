/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import GlobalPhi43.MW20.Setting.MWCylinder
public import GlobalPhi43.MW20.Setting.ParabolicClosedNbhd
public import GlobalPhi43.MW20.Setting.HeatOperator
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# `GlobalPhi43.IsMWLocalData`

The local data sets of the MW20 estimate with smooth defects.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace GlobalPhi43

open RegularityStructures

/-- `(u, ζ, J, Y, Z, e₁, e₂, e₃, C₁, C₂)` is an MW20-D local data set: `u` is smooth on a
neighbourhood of `P̄`; `ζ, J, Y, Z, e₁, e₂, e₃` are smooth on `ℝ × ℝ³`; with `V = J² − C₁` and `W = J³ − 3C₁J`,
`Lu = −u³ + ζ + (3C₁ − 9C₂)u` on `P` and `LJ = ζ + e₁`, `LY = V + e₂`, `LZ = W + e₃` on `P⁺ = P + B̄(0,1)`. -/
def IsMWLocalData (u ζ J Y Z e₁ e₂ e₃ : ParabolicSpace → ℝ) (C₁ C₂ : ℝ) : Prop :=
  (∃ U : Set ParabolicSpace, IsOpen U ∧ closure mwCylinder ⊆ U ∧ ContDiffOn ℝ ∞ u U) ∧
    ContDiff ℝ ∞ ζ ∧ ContDiff ℝ ∞ J ∧ ContDiff ℝ ∞ Y ∧ ContDiff ℝ ∞ Z ∧
    ContDiff ℝ ∞ e₁ ∧ ContDiff ℝ ∞ e₂ ∧ ContDiff ℝ ∞ e₃ ∧
    (∀ z ∈ mwCylinder, heatOperator u z = -u z ^ 3 + ζ z + (3 * C₁ - 9 * C₂) * u z) ∧
    ∀ z ∈ parabolicClosedNbhd mwCylinder 1,
      heatOperator J z = ζ z + e₁ z ∧
        heatOperator Y z = (J z ^ 2 - C₁) + e₂ z ∧
        heatOperator Z z = (J z ^ 3 - 3 * C₁ * J z) + e₃ z

end GlobalPhi43

end
