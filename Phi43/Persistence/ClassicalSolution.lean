/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43Statements.Defs.ExcludedKappa
public import Phi43Statements.Defs.IsModeratePhi43Lift
public import Phi43Statements.Defs.Phi43Size
public import Phi43.ClassicalSolution
public import Phi43.Persistence.AtZero
public import Phi43.Persistence.Positive

/-!
# Persistence of classical solutions

`phi43_persistence` is, verbatim, the first conjunct, persistence, of the conclusion of
`Statements.phi43ClassicalSolution_stoppedContinuity`: classical solutions persist, in `𝒞^η`, for a time
`t₀ ≤ 1` and with a radius `R` depending only on `(L, B)` (and the fixed `κ, N, η`).  It combines
`persist_positive` (start times `s ∈ (0, T]`) with `persistence_at_zero` (start time `s = 0`).
-/

public section

namespace RegularityStructures.Phi43.Persistence

/-- **Clause (i) of `phi43ClassicalSolution_stoppedContinuity`**: persistence of classical
solutions for a time depending only on the level and the size. -/
theorem phi43_persistence (κ : RegularityStructures.Phi43.Kappa)
    (hκE : κ.1 ∉ RegularityStructures.Phi43.Statements.excludedKappa) (N : ℕ) (hN : 5 ≤ N)
    (η : RegularityStructures.NegExponent)
    (hη : (η : ℝ) ∈ Set.Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ))) (hκη : κ.1 < -(1 / 2 : ℝ) - η) :
    (∀ L B : ℝ, 1 ≤ L → 1 ≤ B → ∃ t₀ R : ℝ, 0 < t₀ ∧ t₀ ≤ 1 ∧
      ∀ (f : RegularityStructures.SpaceTime → ℝ)
        (C : RegularityStructures.Phi43.RenormalisationConstants)
        (Z : RegularityStructures.Model
          (RegularityStructures.Phi43.phi43RegularityStructure κ)
          RegularityStructures.parabolicSemigroup)
        (ψ : ℝ → C(RegularityStructures.Torus3, ℝ)) (u₀ : C(RegularityStructures.Torus3, ℝ))
        (u : ℝ → C(RegularityStructures.Torus3, ℝ)) (T : ℝ),
        RegularityStructures.Phi43.Statements.IsModeratePhi43Lift N κ f C Z ψ →
        RegularityStructures.Phi43.IsClassicalSolution (3 * C.1 - 9 * C.2) f u₀ u →
        1 ≤ T → RegularityStructures.Phi43.Statements.phi43Size κ η T Z ψ ≤ ENNReal.ofReal B →
        ∀ s ∈ Set.Icc (0 : ℝ) T, RegularityStructures.holderBesovENorm η (u s) ≤ ENNReal.ofReal L →
          ∀ t ∈ Set.Icc s (s + t₀),
            RegularityStructures.holderBesovENorm η (u t) ≤ ENNReal.ofReal R) := by
  have _ := hκE
  exact persistence_at_zero κ N η
    (persist_positive κ η (by linarith [hη.1]) (by linarith) N (by omega))

end RegularityStructures.Phi43.Persistence

end
