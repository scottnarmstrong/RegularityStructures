/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43Statements.Defs.ExcludedKappa
public import Phi43Statements.Defs.IsModeratePhi43Lift
public import Phi43Statements.Defs.Phi43Size
public import Phi43Statements.Defs.Phi43Dist
public import Phi43.ClassicalSolution
public import Phi43.Steps.ClassicalSolutionStoppedContinuity

/-!
# Persistence and stopped continuity of classical solutions

The deterministic input to Theorem A, stated for classical solutions. Let `κ` avoid the finite set
`excludedKappa`, `N ≥ 5`, `η ∈ (-2/3, -1/2)` and `κ < -1/2 - η`. A smooth noise `f` comes with its
lift `(Z, ψ)` (`IsModeratePhi43Lift`): the renormalised canonical model `Z` of `f` with constants
`C`, and the massive heat potential `ψ` of `f`. Let `u` be the classical solution of the equation
driven by `f` and renormalised with the counterterm `3C₁ - 9C₂`.

1. *Persistence.* A solution that is in the `L`-ball of `𝒞^η` at time `s` stays in an `R`-ball
   up to time `s + t₀`, where `t₀` and `R` depend only on `L` and on a bound `B` for the size
   `phi43Size` of the lift.
2. *Stopped continuity.* On `[0, T]`, as long as two solutions stay in the `L`-ball, their
   distance in `𝒞^η` is at most `ϵ` once the distance `phi43Dist` of their lifts is at most `δ`,
   uniformly over lifts of size at most `B`.

This is the continuity of the maximal solution map in the model [Hai14, Proposition 9.8,
Corollary 7.12], combined with the identification of the reconstructed abstract solution with the
classical solution of the renormalised equation [Hai14, Proposition 9.10]. In the proof of
Theorem A it turns the convergence of the lifts into the convergence of the solutions up to
explosion.

Here `κ ∈ (0, 1/16)` fixes the homogeneity `-5/2 - κ` of the noise symbol `Ξ` in the Φ⁴₃ regularity
structure `phi43RegularityStructure κ`, the cutoff of the fixed point is `γ = gamma κ = 1 + 3κ`, and
`N` fixes the truncated heat kernel `annKernel0C N` of the kernel decomposition [Hai14, Assumption
5.4].

The proof is `RegularityStructures.Phi43.phi43ClassicalSolution_stoppedContinuity`,
in the module `Phi43.Steps.ClassicalSolutionStoppedContinuity`.

Source: [Hai14, Proposition 9.8, Corollary 7.12, Proposition 9.10].
-/

public section

namespace RegularityStructures.Phi43

/-- **Persistence and stopped continuity.** Classical solutions of the renormalised
equations persist for a time that depends only on the level `L` and the size bound `B`. Up to exit
from the `L`-ball, they depend continuously on the lift in the distance `phi43Dist`, uniformly over
lifts of size at most `B`. -/
theorem Statements.phi43ClassicalSolution_stoppedContinuity (κ : RegularityStructures.Phi43.Kappa)
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
            RegularityStructures.holderBesovENorm η (u t) ≤ ENNReal.ofReal R) ∧
    ∀ T L B ϵ : ℝ, 1 ≤ T → 1 ≤ L → 1 ≤ B → 0 < ϵ → ∃ δ : ℝ, 0 < δ ∧
      ∀ (f g : RegularityStructures.SpaceTime → ℝ)
        (C C' : RegularityStructures.Phi43.RenormalisationConstants)
        (Z Z' : RegularityStructures.Model
          (RegularityStructures.Phi43.phi43RegularityStructure κ)
          RegularityStructures.parabolicSemigroup)
        (ψ ψ' : ℝ → C(RegularityStructures.Torus3, ℝ)) (u₀ : C(RegularityStructures.Torus3, ℝ))
        (u v : ℝ → C(RegularityStructures.Torus3, ℝ)),
        RegularityStructures.Phi43.Statements.IsModeratePhi43Lift N κ f C Z ψ →
        RegularityStructures.Phi43.Statements.IsModeratePhi43Lift N κ g C' Z' ψ' →
        RegularityStructures.Phi43.IsClassicalSolution (3 * C.1 - 9 * C.2) f u₀ u →
        RegularityStructures.Phi43.IsClassicalSolution (3 * C'.1 - 9 * C'.2) g u₀ v →
        RegularityStructures.Phi43.Statements.phi43Size κ η T Z ψ ≤ ENNReal.ofReal B →
        RegularityStructures.Phi43.Statements.phi43Size κ η T Z' ψ' ≤ ENNReal.ofReal B →
        RegularityStructures.Phi43.Statements.phi43Dist κ η T Z Z' ψ ψ' ≤ ENNReal.ofReal δ →
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          (∀ s ∈ Set.Icc (0 : ℝ) t,
            RegularityStructures.holderBesovENorm η (u s) ≤ ENNReal.ofReal L ∧
            RegularityStructures.holderBesovENorm η (v s) ≤ ENNReal.ofReal L) →
          RegularityStructures.holderBesovENorm η (u t - v t) ≤ ENNReal.ofReal ϵ :=
  by exact RegularityStructures.Phi43.phi43ClassicalSolution_stoppedContinuity κ hκE N hN η hη hκη

end RegularityStructures.Phi43

end
