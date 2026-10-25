/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup
public import RegularityStructures.Analysis.Semigroup.Pairing.Basic

/-!
# Linearity and increments of the model pairing with scaled test functions

* additivity of `g ↦ ⟨Π_z τ, g⟩` over finite families of scaled test functions at `z`;
* additivity of `τ ↦ ⟨Π_z τ, g⟩` on `T_{<γ}`;
* transport `⟨Π_y τ, g⟩ = ⟨Π_z Γ_{zy} τ, g⟩`;
* the increment bound
  `|⟨Π_z τ, g⟩ - ⟨Π_y τ', g⟩| ≤ C (A R⁵) ∑_i |(τ - Γ_{zy} τ')_i| R^{deg i}`.

Source: [Hai14] = arXiv:1303.5113v4, (2.15), Proposition 7.2.
-/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace RegularityStructures

namespace Model

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  (M : Model 𝒯 parabolicSemigroup) {γ CPi CGam : ℝ} {g : ParabolicSpace → ℝ}
  {z : ParabolicSpace} {R A : ℝ}

/-- Transport: `Π_y τ = Π_z Γ_{zy} τ`. -/
theorem pairing_regPi_eq_gammaMap (y z : ParabolicSpace) (τ : ι → ℝ)
    (g : ParabolicSpace → ℝ) :
    parabolicSemigroup.pairing (M.regPi y τ) g =
      parabolicSemigroup.pairing (M.regPi z (M.gammaMap z y τ)) g := by
  have : M.regPi z (M.gammaMap z y τ) = M.regPi y τ := by
    funext t w; exact M.regPi_gammaMap z y τ t w
  rw [this]

end Model

end RegularityStructures

end
