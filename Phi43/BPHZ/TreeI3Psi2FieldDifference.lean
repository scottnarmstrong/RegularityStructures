/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2FieldCov

/-!
# The tree `I(Ψ³) Ψ²`: covariance of the two-scale difference

Write `hairerI3Psi2Cov N ρ x a b y y'` for the right-hand side of
`hairerI3Psi2Field_integral_mul`, i.e. the chaos-`5`, `3`, `1` double integrals, minus the two
cross terms with the counterterm `-3 C₂ Ψ`, plus `9 C₂^a C₂^b Q_{ab}(y - y')`.  It is the
covariance `E[F_a(y) F_b(y')]` for noises at scales `a`, `b`.  For two scales `a`, `b` and noises
`ξ`, `ξ'` of the same white noise,
`E[(F_a - F_b)(y) (F_a - F_b)(y')] = Cov(a,a) - Cov(a,b) - Cov(b,a) + Cov(b,b)`
[Hai14, (10.3) for `τ = I(Ψ³) Ψ²`].  The cross-scale terms are the chaos kernels with entries
`Q_{ab}`.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

/-- The covariance `E[F_a(y) F_b(y')]` of the field `hairerI3Psi2Field` at scales `a`, `b`: chaos
`5`, `3`, `1` of the main product, the two cross terms with `-3 C₂ Ψ`, and the `9 C₂ C₂ Q` term. -/
def hairerI3Psi2Cov (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (x : SpaceTime) (a b : ℝ)
    (y y' : SpaceTime) : ℝ :=
  (∫ q : SpaceTime × SpaceTime, hairerI2Psi2Kernel N x y q.1 * hairerI2Psi2Kernel N x y' q.2 *
    hairerI3Psi2Chaos5 N ρ a a b b y y' q.1 q.2) +
  (∫ q : SpaceTime × SpaceTime, hairerI2Psi2Kernel N x y q.1 * hairerI2Psi2Kernel N x y' q.2 *
    hairerI3Psi2Chaos3 N ρ a a b b y y' q.1 q.2) +
  (∫ q : SpaceTime × SpaceTime, hairerI2Psi2Kernel N x y q.1 * hairerI2Psi2Kernel N x y' q.2 *
    hairerI3Psi2Chaos1 N ρ a a b b y y' q.1 q.2) -
  3 * hairerSunsetConstant N ρ b *
    (∫ w, hairerI2Psi2Kernel N x y w * hairerI3Psi2CrossKernel N ρ a a b y y' w) -
  3 * hairerSunsetConstant N ρ a *
    (∫ w, hairerI2Psi2Kernel N x y' w * hairerI3Psi2CrossKernel N ρ b b a y' y w) +
  9 * hairerSunsetConstant N ρ a * hairerSunsetConstant N ρ b *
    hairerCrossCovariance N ρ a b (y - y')

end RegularityStructures.Phi43

end

