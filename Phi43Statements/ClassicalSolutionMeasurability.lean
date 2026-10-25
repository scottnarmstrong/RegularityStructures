/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.ClassicalSolution.Measurable

/-!
# Measurability of solutions driven by a regularised noise

If `u ω` is the classical solution driven by `ξ ω` for a regularised noise `ξ`, then for every
`t ≥ 0` the map `ω ↦ u ω t ∈ 𝒞^η` is measurable. This follows from the continuous dependence of
the classical solution on the forcing.

This is item (W5) of Lemma 4.1 of the statement. Items (W1)–(W5) show that Theorem A is not vacuous:
the white noises, regularised noises and classical solutions over which it quantifies exist, and its
conditions are meaningful. This file states the second half of item (W5).

The proof is `RegularityStructures.Phi43.classicalSolution_measurable`,
in the module `Phi43.ClassicalSolution.Measurable`.

Source: the statement, Lemma 4.1 (W5).
-/

public section

namespace RegularityStructures.Phi43.Statements

open MeasureTheory Set
open scoped ENNReal

/-- **Measurable solutions** (Lemma 4.1 (W5), second half). Solutions driven by a regularised
noise are measurable in `ω`. -/
theorem classicalSolution_measurable :
    ∀ (η : NegExponent) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (W : (SpaceTime → ℝ) → Ω → ℝ)
    (_hW : IsWhiteNoise P W) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (_hρ : IsMollifier ρ) {ε : ℝ}
    (_hε : ε ∈ Ioc (0 : ℝ) 1) (ξ : Ω → SpaceTime → ℝ) (_hξ : IsRegularisedNoise P W ρ ε ξ)
    (c : ℝ) (u₀ : C(Torus3, ℝ)) (_hu₀ : IsSmoothOnTorus u₀) (u : Ω → ℝ → C(Torus3, ℝ))
    (_hu : ∀ ω, IsClassicalSolution c (ξ ω) u₀ (u ω)) {t : ℝ} (_ht : 0 ≤ t),
    Measurable fun ω => toHolderBesov η (u ω t) :=
  by exact RegularityStructures.Phi43.classicalSolution_measurable

end RegularityStructures.Phi43.Statements

end
