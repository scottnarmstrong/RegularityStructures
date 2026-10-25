/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.FixedPointMaximal

/-!
# Global solutions under an a priori bound

The statement `RegularityStructures.Statements.exists_global_solution_of_bound`.
Its proof is `RegularityStructures.exists_global_solution_of_bound`,
in the module `RegularityStructures.Abstract.FixedPointMaximal`.
-/

public section

namespace RegularityStructures

/-- **Global existence under an a priori bound**: under the hypotheses of `exists_maximal_solution`,
if the size of every solution stays below a fixed bound, the maximal solution exists for all
times. -/
theorem Statements.exists_global_solution_of_bound.{u_1} :
    ∀ {𝒮 : Type u_1} (size : 𝒮 → ℝ) (Sol : 𝒮 → ℝ → (ℝ → 𝒮) → Prop),
      (∀ (a : 𝒮) (T : ℝ) (u w : ℝ → 𝒮), Sol a T u → (∀ t ∈ Set.Icc 0 T, u t = w t) → Sol a T w) →
        (∀ (a : 𝒮) (T T' : ℝ) (u : ℝ → 𝒮), Sol a T u → 0 < T' → T' ≤ T → Sol a T' u) →
          (∀ (a : 𝒮) (T : ℝ) (u w : ℝ → 𝒮), Sol a T u → Sol a T w → ∀ t ∈ Set.Icc 0 T, u t = w t) →
            (∀ (L : ℝ), ∃ τ > 0, ∀ (a : 𝒮), size a ≤ L → ∃ (u : ℝ → 𝒮), Sol a τ u) →
              (∀ (a : 𝒮) (s T : ℝ) (u w : ℝ → 𝒮),
                  0 < s →
                    0 < T → Sol a s u → Sol (u s) T w → Sol a (s + T) fun (t : ℝ) => if t ≤ s then u t else w (t - s)) →
                ∀ (a : 𝒮) {B : ℝ},
                  (∀ (T : ℝ) (u : ℝ → 𝒮), 0 < T → Sol a T u → ∀ t ∈ Set.Icc 0 T, size (u t) ≤ B) →
                    ∃ (u : ℝ → 𝒮), ∀ (T : ℝ), 0 < T → Sol a T u :=
  by exact RegularityStructures.exists_global_solution_of_bound

end RegularityStructures

end
