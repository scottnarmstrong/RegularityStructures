/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.CanonicalBridgeData
public import Phi43.BPHZ.CanonicalBridgeFields
public import Phi43.BPHZ.TreeFormulas

/-!
# The canonical lift on `ℝ⁴` is the pathwise tree field on `ℝ × T³`

For `D = hairerCanonicalData N noise` with `noise.zeta = ξ ω ∘ proj`, the renormalised realisation
`D.renormalisedPi C x (basis τ)` of each tree `τ ∈ F₋` (other than `Ψ²Xᵢ`, see below) is the
pathwise tree field of `Phi43/BPHZ/Tree*.lean` evaluated at `proj x`, `proj y`, with constants
`(C₁, C₂) = C`.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- The pathwise tree fields on `F₋` (except `Ψ²Xᵢ`) as a function of the symbol, with arbitrary
constants `c₁ c₂` and base point `x`; `0` on the other symbols. -/
def hairerTreeField {Ω : Type*} (N : ℕ) (ξ : Ω → SpaceTime → ℝ) (c₁ c₂ : ℝ) (x : SpaceTime)
    (ω : Ω) : Symbol → SpaceTime → ℝ
  | .noise => ξ ω
  | .psi => hairerPsiField N ξ ω
  | .psiSq => hairerTreePsiSq N ξ c₁ ω
  | .psiCube => hairerTreePsiCube N ξ c₁ ω
  | .iPsiCubePsi => hairerTreeI3Psi N ξ c₁ x ω
  | .iPsiSqPsiSq => hairerTreeI2Psi2 N ξ c₁ c₂ x ω
  | .iPsiCubePsiSq => hairerTreeI3Psi2 N ξ c₁ c₂ x ω
  | _ => fun _ => 0

end RegularityStructures.Phi43

end

