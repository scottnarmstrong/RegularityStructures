/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.ClassicalSolution.Existence
public import Phi43.ClassicalSolution.Uniqueness

/-!
# Item (W4) of Lemma 4.1: classical well-posedness of the regularised equation

Item (W4) of Lemma 4.1 of the statement. For smooth forcing `f` and smooth initial data `u₀`, the
equation `∂_t u = Δu − u³ + c u + f`, `u(0) = u₀`, has exactly one classical solution on
`[0, ∞) × T³`. Existence is `classicalSolution_exists`; uniqueness is `classicalSolution_unique`.
-/

public section

namespace RegularityStructures.Phi43

/-- **(W4)** The regularised equation has exactly one classical solution. -/
theorem classicalSolution_exists_unique (c : ℝ) {f : SpaceTime → ℝ} (hf : IsSmoothOnSpaceTime f)
    {u₀ : C(Torus3, ℝ)} (hu₀ : IsSmoothOnTorus u₀) :
    (∃ u, IsClassicalSolution c f u₀ u) ∧
      ∀ u u', IsClassicalSolution c f u₀ u → IsClassicalSolution c f u₀ u' →
        ∀ t, 0 ≤ t → u t = u' t :=
  ⟨classicalSolution_exists c hf hu₀, fun _ _ hu hu' => classicalSolution_unique c hu hu'⟩

end RegularityStructures.Phi43

end
