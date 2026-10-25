/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeWickSquare

/-!
# The tree `I(Ψ²) Ψ²`: the field (10.39)

For a base point `x`, the renormalised model of `τ = I(Ψ²) Ψ²` is [Hai14, (10.39)]
`(Π̂^ε_x τ)(y) = ((K ∗ :ψ_ε²:)(y) - (K ∗ :ψ_ε²:)(x)) :ψ_ε²:(y) - C₂^{ε,K}`, i.e.
`hairerI2Psi2Field N ρ ε ξ x ω y = (∫ (K(y - w) - K(x - w)) :Ψ²:(w) dw) :Ψ²:(y) - C₂`
with `K = hairerKernelTorus N` and `C₂ = hairerSunsetConstant N ρ ε`.

**Comparison with the renormalised tree formula.**  `renormalisedPi_basis_iPsiSqPsiSq_eq` gives
`integrate(Ψ²)(y) · (Ψ(y)² - C₁) - C₂` where `integrate(Ψ²)(y)` is `K ∗ Ψ²(y) - K ∗ Ψ²(x)`
(the Taylor polynomial of degree `< 1 - 2κ` is the constant `K ∗ Ψ²(x)`).  Because
`∫ (K(y - w) - K(x - w)) dw = 0` (`integral_hairerI2Psi2Kernel`), subtracting the constant `C₁`
inside the convolution changes nothing, so the two expressions agree.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

/-- The kernel increment `w ↦ K(y - w) - K(x - w)` of the tree `I(Ψ²)` at base point `x`. -/
def hairerI2Psi2Kernel (N : ℕ) (x y w : SpaceTime) : ℝ :=
  hairerKernelTorus N (y - w) - hairerKernelTorus N (x - w)

/-- **The field `(Π̂^ε_x τ)(y)` of the tree `τ = I(Ψ²) Ψ²`**, [Hai14, (10.39)]. -/
def hairerI2Psi2Field {Ω : Type*} (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ)
    (ξ : Ω → SpaceTime → ℝ) (x : SpaceTime) (ω : Ω) (y : SpaceTime) : ℝ :=
  (∫ w, hairerI2Psi2Kernel N x y w * hairerPsiWickSquare N ρ ε ξ ω w) *
    hairerPsiWickSquare N ρ ε ξ ω y - hairerSunsetConstant N ρ ε

end RegularityStructures.Phi43

end

public section

open MeasureTheory

namespace RegularityStructures.Phi43

/-- The kernel increment is integrable. -/
theorem integrable_hairerI2Psi2Kernel (N : ℕ) (x y : SpaceTime) :
    Integrable (hairerI2Psi2Kernel N x y) :=
  (integrable_hairerKernelTorus_sub N y).sub (integrable_hairerKernelTorus_sub N x)

/-- The kernel increment is measurable. -/
theorem measurable_hairerI2Psi2Kernel (N : ℕ) (x y : SpaceTime) :
    Measurable (hairerI2Psi2Kernel N x y) :=
  ((measurable_constantsComparison_hairerKernelTorus N).comp
      (measurable_const.sub measurable_id)).sub
    ((measurable_constantsComparison_hairerKernelTorus N).comp
      (measurable_const.sub measurable_id))

/-- The kernel increment has integral zero: `∫ (K(y - w) - K(x - w)) dw = 0`. -/
theorem integral_hairerI2Psi2Kernel (N : ℕ) (x y : SpaceTime) :
    ∫ w, hairerI2Psi2Kernel N x y w = 0 := by
  unfold hairerI2Psi2Kernel
  rw [integral_sub (integrable_hairerKernelTorus_sub N y) (integrable_hairerKernelTorus_sub N x),
    integral_comp_sub_left_spaceTime (hairerKernelTorus N) y,
    integral_comp_sub_left_spaceTime (hairerKernelTorus N) x, sub_self]

end RegularityStructures.Phi43

end
