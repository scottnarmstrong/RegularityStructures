/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.FixedPointMaximal

/-!
# Maximal solutions and the blow-up alternative

The statement `RegularityStructures.Statements.exists_maximal_solution`.
Its proof is `RegularityStructures.exists_maximal_solution`,
in the module `RegularityStructures.Abstract.FixedPointMaximal`.
-/

public section

namespace RegularityStructures

/-- **Maximal solutions and the blow-up alternative for an abstract solution relation**, the
patching argument behind [Hai14, Proposition 7.11] and the discussion after it; it is not
Proposition 7.11 itself, which is the instance for the fixed point of [Hai14, Section 7]. Under local existence with a time depending only on the size of the datum, local
uniqueness, restriction and gluing, every datum has a solution on `[0, T*)` that extends every
other solution, and if `T* < ∞` the size of the restart datum tends to infinity at `T*`. -/
theorem Statements.exists_maximal_solution.{u_1} :
    ∀ {𝒮 : Type u_1} (size : 𝒮 → ℝ) (Sol : 𝒮 → ℝ → (ℝ → 𝒮) → Prop),
      (∀ (a : 𝒮) (T : ℝ) (u w : ℝ → 𝒮), Sol a T u → (∀ t ∈ Set.Icc 0 T, u t = w t) → Sol a T w) →
        (∀ (a : 𝒮) (T T' : ℝ) (u : ℝ → 𝒮), Sol a T u → 0 < T' → T' ≤ T → Sol a T' u) →
          (∀ (a : 𝒮) (T : ℝ) (u w : ℝ → 𝒮), Sol a T u → Sol a T w → ∀ t ∈ Set.Icc 0 T, u t = w t) →
            (∀ (L : ℝ), ∃ τ > 0, ∀ (a : 𝒮), size a ≤ L → ∃ (u : ℝ → 𝒮), Sol a τ u) →
              (∀ (a : 𝒮) (s T : ℝ) (u w : ℝ → 𝒮),
                  0 < s →
                    0 < T → Sol a s u → Sol (u s) T w → Sol a (s + T) fun (t : ℝ) => if t ≤ s then u t else w (t - s)) →
                ∀ (a : 𝒮),
                  ∃ (Tstar : ENNReal) (u : ℝ → 𝒮),
                    0 < Tstar ∧
                      (∀ (T : ℝ), 0 < T → ENNReal.ofReal T < Tstar → Sol a T u) ∧
                        (∀ (T : ℝ),
                            0 < T → ∀ (w : ℝ → 𝒮), Sol a T w → ENNReal.ofReal T < Tstar ∧ ∀ t ∈ Set.Icc 0 T, w t = u t) ∧
                          (Tstar ≠ ⊤ →
                            Filter.Tendsto (fun (t : ℝ) => size (u t)) (nhdsWithin Tstar.toReal (Set.Iio Tstar.toReal))
                              Filter.atTop) :=
  by exact RegularityStructures.exists_maximal_solution

end RegularityStructures

end
