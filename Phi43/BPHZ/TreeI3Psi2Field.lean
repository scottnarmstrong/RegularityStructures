/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2Field
public import Phi43.BPHZ.TreeWickCube

/-!
# The tree `I(Ψ³) Ψ²`: the field

For a base point `x`, the renormalised model of `τ = I(Ψ³) Ψ²` is [Hai14, p. 170-171]
`(Π̂^ε_x τ)(y) = ((K ∗ :ψ_ε³:)(y) - (K ∗ :ψ_ε³:)(x)) :ψ_ε²:(y) - 3 C₂^{ε,K} ψ_ε(y)`, i.e.
`hairerI3Psi2Field N ρ ε ξ x ω y = (∫ (K(y - w) - K(x - w)) :Ψ³:(w) dw) :Ψ²:(y) - 3 C₂ Ψ(y)`
with `K = hairerKernelTorus N` and `C₂ = hairerSunsetConstant N ρ ε`.  The kernel increment is
`hairerI2Psi2Kernel N x y`, the same as for the tree `I(Ψ²) Ψ²`.

**Comparison with the renormalised tree formula.**  `renormalisedPi_basis_iPsiCubePsiSq_eq` gives
`(Ψ(y) Ψ(y) - C₁) (integrate(Ψ³)(y) - 3 C₁ integrate(Ψ)(y)) - 3 C₂ Ψ(y)` where `integrate(f)(y)` is
`K ∗ f(y) - K ∗ f(x)`.  When both kernel integrals converge, this is `hairerI3Psi2Field`.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

/-- **The field `(Π̂^ε_x τ)(y)` of the tree `τ = I(Ψ³) Ψ²`**, [Hai14, p. 170-171]. -/
def hairerI3Psi2Field {Ω : Type*} (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ)
    (ξ : Ω → SpaceTime → ℝ) (x : SpaceTime) (ω : Ω) (y : SpaceTime) : ℝ :=
  (∫ w, hairerI2Psi2Kernel N x y w * hairerPsiWickCube N ρ ε ξ ω w) *
    hairerPsiWickSquare N ρ ε ξ ω y - 3 * hairerSunsetConstant N ρ ε * hairerPsiField N ξ ω y

end RegularityStructures.Phi43

end

