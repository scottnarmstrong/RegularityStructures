/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovPiHalfAssemblyUnitBox
public import RegularityStructures.Probability.ModelKolmogorovPiHalfAssemblyBox

/-!
# The `Π` half of the Kolmogorov criterion for models

`randomModel_piHalf`: the `Π`-half input `hPiHalf` of
`kolmogorov_modelNorm_of_halves`, for every compact `S`, with `qPi ≥ p` and `KPi` chosen from the
structure data and `p` only (before `Cbar`).  `PiHalfStmt` unfolds, by definition, to the premise
`hPiHalf` of `kolmogorov_modelNorm_of_halves` (same binders and hypotheses).

The proof: unit-box case (`piHalfStmt_unitBox`) from the cell-block reduction, the
deterministic/random split of the cell weights, the dyadic union bound and the proved `Γ` half;
then general compact sets by finite translated unit-box pieces (`piHalfStmt_of_unitBox`).
-/

public section

namespace RegularityStructures

universe u

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem randomModel_piHalf (𝒯 : RegularityStructure ι) (γ κbar θ : ℝ)
    (hκbar : 0 < κbar) (hθ : 0 ≤ θ) (Dπ : Set ι) (DΓ : Set (ι × ι)) (S : Set ParabolicSpace)
    (hS : IsCompact S) (p : ℕ) (hp : 1 ≤ p) :
    ∃ qPi : ℕ, p ≤ qPi ∧ ∃ KPi : ℝ → ℝ, (∀ Cbar, 0 ≤ KPi Cbar) ∧
      PiHalfStmt.{u, _} 𝒯 γ κbar θ Dπ DΓ S p qPi KPi :=
  piHalfStmt_of_unitBox.{u} 𝒯 γ κbar θ Dπ DΓ S hS p hp fun T hT hTb =>
    piHalfStmt_unitBox.{u} 𝒯 γ κbar θ hκbar hθ Dπ DΓ T hT hTb p hp

end RegularityStructures

end
