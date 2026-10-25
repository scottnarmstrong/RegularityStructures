/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.ClassicalSolution.PathContinuity

/-!
# Continuity of classical-solution paths in `𝒞^η`

Every classical solution `u` of `∂_t u = Δu - u³ + c u + f` is a continuous path
`t ↦ u(t) ∈ 𝒞^η` on `[0, ∞)`. This follows from `‖·‖_η ≤ ‖·‖_∞` and the uniform continuity of `u`
on compact sets.

This is item (W5) of Lemma 4.1 of the statement. Items (W1)–(W5) show that Theorem A is not vacuous:
the white noises, regularised noises and classical solutions over which it quantifies exist, and its
conditions are meaningful. This file states the first half of item (W5).

The proof is `RegularityStructures.Phi43.classicalSolution_continuousOn`,
in the module `Phi43.ClassicalSolution.PathContinuity`.

Source: the statement, Lemma 4.1 (W5).
-/

public section

namespace RegularityStructures.Phi43.Statements

open MeasureTheory Set
open scoped ENNReal

/-- **Continuous paths** (Lemma 4.1 (W5), first half). Classical solutions are continuous
paths into `𝒞^η`. -/
theorem classicalSolution_continuousOn :
    ∀ (η : NegExponent) {c : ℝ} {f : SpaceTime → ℝ}
    {u₀ : C(Torus3, ℝ)} {u : ℝ → C(Torus3, ℝ)} (_hu : IsClassicalSolution c f u₀ u),
    ContinuousOn (fun t => toHolderBesov η (u t)) (Ici 0) :=
  by exact RegularityStructures.Phi43.classicalSolution_continuousOn

end RegularityStructures.Phi43.Statements

end
