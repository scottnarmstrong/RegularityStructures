/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.TheoremA

/-!
# Theorem A: renormalised dynamical Φ⁴₃ on the three-torus

Let `ξ_ε` be a mollified space-time white noise on `ℝ × T³`, and let `u_ε` solve
`∂_t u_ε = Δu_ε - u_ε³ + (a + 3C₁^ε - 9C₂^ε) u_ε + ξ_ε`, `u_ε(0) = u₀`,
with the explicit renormalisation constants `C₁^ε`, `C₂^ε` of Definition 2.5 of the statement.
Then `u_ε` converges in probability in `𝒞^η`, `η ∈ (-2/3, -1/2)`, up to the explosion time of
the limit, and the limit does not depend on the mollifier.

This is Theorem A of the statement. It is a version of [Hai14, Theorem 1.15] with smooth initial
data, with explicit constants built from the massive heat kernel instead of constants that are
only asserted to exist, and with convergence up to the maximal existence time of the limit.

The proof is `RegularityStructures.Phi43.theoremA`,
in the module `Phi43.TheoremA`.

Source: the statement, Theorem A; [Hai14, Theorem 1.15].
-/

public section

namespace RegularityStructures.Phi43.Statements

open MeasureTheory Set
open scoped ENNReal

/-- **Theorem A.** Let `W` be a space-time white noise, `a ∈ ℝ`, `u₀` smooth on `T³`,
`η ∈ (-2/3, -1/2)` and `ρ` a mollifier. For `ε ∈ (0, 1]` let `ξ ε` be a regularised noise at
scale `ε`, and let `u ε ω` be the classical solution, driven by `ξ ε ω`, of the equation with
counterterm `a + 3C₁^ε - 9C₂^ε` (`wickConstant`, `sunsetConstant`). Then there are a random time
`τ` and paths `v` that satisfy conditions (A1)–(A3) of the statement (`IsPhi43Limit`), and
condition (A4) holds: for every other mollifier `ρ'`, with regularised noises `ξ'` driven by the
same `W`, solutions `u'` and a pair `(τ', v')` that satisfies (A1)–(A3) for them, one has
`τ' = τ` almost surely, and almost surely `v' t = v t` for every `t < τ`. -/
theorem theoremA :
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W)
    (a : ℝ) (u₀ : C(Torus3, ℝ)) (hu₀ : IsSmoothOnTorus u₀)
    (η : NegExponent) (hη : (η : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    (ξ : ℝ → Ω → SpaceTime → ℝ) (hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε))
    (u : ℝ → Ω → ℝ → C(Torus3, ℝ))
    (hu : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ ω, IsClassicalSolution
      (a + 3 * wickConstant ρ ε - 9 * sunsetConstant ρ ε) (ξ ε ω) u₀ (u ε ω)),
    ∃ (τ : Ω → ℝ≥0∞) (v : Ω → ℝ → HolderBesov η),
      IsPhi43Limit P η u₀ u τ v ∧
      ∀ (ρ' : ℝ × (Fin 3 → ℝ) → ℝ) (ξ' : ℝ → Ω → SpaceTime → ℝ)
        (u' : ℝ → Ω → ℝ → C(Torus3, ℝ)) (τ' : Ω → ℝ≥0∞) (v' : Ω → ℝ → HolderBesov η),
        IsMollifier ρ' →
        (∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ' ε (ξ' ε)) →
        (∀ ε ∈ Ioc (0 : ℝ) 1, ∀ ω, IsClassicalSolution
          (a + 3 * wickConstant ρ' ε - 9 * sunsetConstant ρ' ε) (ξ' ε ω) u₀ (u' ε ω)) →
        IsPhi43Limit P η u₀ u' τ' v' →
        τ' =ᵐ[P] τ ∧ ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → ENNReal.ofReal t < τ ω → v' ω t = v ω t :=
  by exact RegularityStructures.Phi43.theoremA

end RegularityStructures.Phi43.Statements

end
