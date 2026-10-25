/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.ClassicalSolution.WellPosed

/-!
# Existence and uniqueness of classical solutions

For every smooth forcing `f` on `ℝ × T³`, constant `c ∈ ℝ` and smooth initial datum `u₀`, the
equation `∂_t u = Δu - u³ + c u + f`, `u(0) = u₀`, has exactly one classical solution in the
sense of Definition 2.6 of the statement (`IsClassicalSolution`). The proof uses local existence
and the comparison bound that the cubic term provides.

This is item (W4) of Lemma 4.1 of the statement. Items (W1)–(W5) show that Theorem A is not vacuous:
the white noises, regularised noises and classical solutions over which it quantifies exist, and its
conditions are meaningful.

The proof is `RegularityStructures.Phi43.classicalSolution_exists_unique`,
in the module `Phi43.ClassicalSolution.WellPosed`.

Source: the statement, Lemma 4.1 (W4), Definition 2.6.
-/

public section

namespace RegularityStructures.Phi43.Statements

open MeasureTheory Set
open scoped ENNReal

/-- **Classical well-posedness** (Lemma 4.1 (W4)). The regularised equation has exactly one
classical solution. -/
theorem classicalSolution_exists_unique :
    ∀ (c : ℝ) {f : SpaceTime → ℝ} (_hf : IsSmoothOnSpaceTime f)
    {u₀ : C(Torus3, ℝ)} (_hu₀ : IsSmoothOnTorus u₀),
    (∃ u, IsClassicalSolution c f u₀ u) ∧
      ∀ u u', IsClassicalSolution c f u₀ u → IsClassicalSolution c f u₀ u' →
        ∀ t, 0 ≤ t → u t = u' t :=
  by exact RegularityStructures.Phi43.classicalSolution_exists_unique

end RegularityStructures.Phi43.Statements

end
