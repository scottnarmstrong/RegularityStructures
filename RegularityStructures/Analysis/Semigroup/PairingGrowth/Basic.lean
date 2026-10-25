/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.Pairing.Main
public import Mathlib.Analysis.InnerProductSpace.Basic
public import RegularityStructures.Analysis.Semigroup.Basic

/-!
# Local order with polynomial growth: definitions

`IsLocalOrderGrowth Λ x₀ γ A C q`: `|Λ_u(y)| ≤ C (1 + d(y, x₀))^q ∑_{a ∈ A} u^{a/ℓ} d(y, x₀)^{γ-a}`
for `0 < u ≤ 1` and all `y`: the weighted analogue of `IsLocalOrder` (`q = 0` recovers it).

Test functions are supported in a ball of radius `λ ≤ 1`, where `(1 + d)^q ≤ 2^q`; the global
growth is only used for integrability. `LocalBall` packages exactly what the proof of the
test-function bound uses: the bound on the ball of radius `lam` and a uniform bound on the kernel
moments against `|Λ_s|`, from points of that ball.

Source: [Hai14] = arXiv:1303.5113v4, Theorem 3.10.
-/

@[expose] public noncomputable section

namespace RegularityStructures.RegularisingSemigroup

open MeasureTheory

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)

/-- `Λ` is of order `γ` at `x₀` with exponents `A` and polynomial growth `q`:
`|Λ_u(y)| ≤ C (1 + d(y, x₀))^q ∑_{a ∈ A} u^{a/ℓ} d(y, x₀)^{γ - a}` for `0 < u ≤ 1`. -/
def IsLocalOrderGrowth (Λ : ℝ → E → ℝ) (x₀ : E) (γ : ℝ) (A : Finset ℝ) (C q : ℝ) : Prop :=
  ∀ u ∈ Set.Ioc (0 : ℝ) 1, ∀ y,
    |Λ u y| ≤ C * (1 + K.scaleDist y x₀) ^ q *
      ∑ a ∈ A, u ^ (a / K.order) * K.scaleDist y x₀ ^ (γ - a)

/-- The hypotheses used on `Λ` for a test function supported in `{d(·, x₀) ≤ lam}`: the
local-order bound with constant `C` on that ball, and a uniform bound for
`∫ |Q_v(y, z)| |Λ_s(z)| dz`, `v ≤ h₀`, `d(y, x₀) ≤ lam`. -/
structure LocalBall (Λ : ℝ → E → ℝ) (x₀ : E) (γ : ℝ) (A : Finset ℝ) (C lam : ℝ) : Prop where
  mem : Λ ∈ K.distributions
  meas : ∀ u, 0 < u → Measurable (Λ u)
  nonneg : 0 ≤ C
  le : ∀ a ∈ A, a ≤ γ
  ball : ∀ u ∈ Set.Ioc (0 : ℝ) 1, ∀ y, K.scaleDist y x₀ ≤ lam →
    |Λ u y| ≤ C * ∑ a ∈ A, u ^ (a / K.order) * lam ^ (γ - a)
  kernel_int : ∀ s ∈ Set.Ioc (0 : ℝ) 1, ∀ h₀ : ℝ, ∃ W : ℝ, ∀ v ∈ Set.Ioc (0 : ℝ) h₀, ∀ y,
    K.scaleDist y x₀ ≤ lam → ∫ z, |K.kernel v y z| * |Λ s z| ∂μ ≤ W

variable {K}

theorem LocalBall.abs_le {Λ : ℝ → E → ℝ} {x₀ : E} {γ : ℝ} {A : Finset ℝ} {C lam : ℝ}
    (hΛ : K.LocalBall Λ x₀ γ A C lam) {u : ℝ} (hu : u ∈ Set.Ioc (0 : ℝ) 1) {y : E}
    (hy : K.scaleDist y x₀ ≤ lam) :
    |Λ u y| ≤ C * ∑ a ∈ A, u ^ (a / K.order) * lam ^ (γ - a) :=
  hΛ.ball u hu y hy

end RegularityStructures.RegularisingSemigroup

end
