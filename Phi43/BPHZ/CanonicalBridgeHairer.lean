/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.CanonicalBridgeRealises
public import Phi43.Structure.CanonicalModel

/-!
# The realisation of `Ψ²Xᵢ` for `hairerCanonicalData`

For the lifted noise `noise.zeta = ξ ω ∘ proj`, the realisation of the symbol `Ψ²Xᵢ` under
`renormalisedPi` of `hairerCanonicalData` is `Ψ²(proj y) (yᵢ - xᵢ)`. Unlike the other symbols, it
uses the `ℝ³`-coordinates of `y` and `x` and is not a function of the projections alone.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

local notation "E" => ParabolicSpace

namespace CanonicalData

variable {κ : Kappa} {Ω : Type*} {N : ℕ} {ξ : Ω → SpaceTime → ℝ} {ω : Ω}
  {noise : CanonicalNoise} (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) (x : E)

/-- The Hairer constants `C = (c_ε, C₂)`. -/
local notation "CH" => ((hairerWickConstant N ρ ε, hairerSunsetConstant N ρ ε) :
  RenormalisationConstants)

variable (C : RenormalisationConstants)

/-- `Ψ²Xᵢ`: the realisation on `ℝ⁴` uses the `ℝ³`-displacement `yᵢ - xᵢ` (not a function of the
projections alone). -/
theorem hairerCanonicalData_renormalisedPi_basis_psiSqX_eq
    (hn : ∀ z, noise.zeta z = ξ ω (spaceTimeProj z)) (hξ : IsSmoothOnSpaceTime (ξ ω))
    (i : Fin 3) :
    (hairerCanonicalData (κ := κ) N noise).renormalisedPi C x (basis (.psiSqX i)) =
      fun y => hairerTreePsiSq N ξ (C₁ C) ω (spaceTimeProj y) * (y.2 i - x.2 i) := by
  rw [renormalisedPi_basis_psiSqX_eq, hairerCanonicalData_localPsi_eq κ N ξ ω hn hξ]
  funext y
  have hc : ∀ (z : E) (j : Fin 3), parabolicCoords z j.succ = z.2 j := by
    intro z j
    fin_cases j <;> rfl
  simp only [hairerTreePsiSq, relCoord, hc]
  ring

end CanonicalData

end RegularityStructures.Phi43

end
