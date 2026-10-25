/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.RegularisedNoise.SmoothVersion.ExistsUnique

/-!
# Existence and uniqueness of regularised noises

For every white noise `W`, mollifier `ρ` and scale `ε ∈ (0, 1]`, a regularised noise at scale `ε`
in the sense of Definition 2.4 of the statement exists: a version of `z ↦ W(ρ_{ε,z})` that is
smooth in `z` for every `ω`. Any two regularised noises are indistinguishable, and every
regularised noise is jointly measurable on `Ω × (ℝ × T³)`.

This is item (W2) of Lemma 4.1 of the statement. Items (W1)–(W5) show that Theorem A is not vacuous:
the white noises, regularised noises and classical solutions over which it quantifies exist, and its
conditions are meaningful.

The proof is `RegularityStructures.Phi43.regularisedNoise_exists_unique`,
in the module `Phi43.RegularisedNoise.SmoothVersion.ExistsUnique`.

Source: the statement, Lemma 4.1 (W2), Definition 2.4.
-/

public section

namespace RegularityStructures.Phi43.Statements

open MeasureTheory Set
open scoped ENNReal

/-- **Regularised noises** (Lemma 4.1 (W2)). Regularised noises exist, are unique up to
indistinguishability, and are jointly measurable. -/
theorem regularisedNoise_exists_unique :
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : (SpaceTime → ℝ) → Ω → ℝ) (_hW : IsWhiteNoise P W)
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (_hρ : IsMollifier ρ) {ε : ℝ} (_hε : ε ∈ Ioc (0 : ℝ) 1),
    (∃ ξ, IsRegularisedNoise P W ρ ε ξ) ∧
      (∀ ξ ξ', IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ ε ξ' →
        ∀ᵐ ω ∂P, ξ ω = ξ' ω) ∧
      ∀ ξ, IsRegularisedNoise P W ρ ε ξ → Measurable fun p : Ω × SpaceTime => ξ p.1 p.2 :=
  by exact RegularityStructures.Phi43.regularisedNoise_exists_unique

end RegularityStructures.Phi43.Statements

end
