/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import GlobalPhi43Statements.Defs.IsGlobalPhi43Flow
public import GlobalPhi43.Proofs.GlobalDynamics

/-!
# Global dynamics of the Φ⁴₃ equation

The global flow of the renormalised dynamical Φ⁴₃ model on `T³`, coming down from infinity, the
Markov and Feller property, the invariant measure and the stationary solution: the clauses
(B1)–(B8) of `GlobalPhi43.IsGlobalPhi43Flow`, after Mourrat–Weber, *The dynamic Φ⁴₃ model comes
down from infinity* (Commun. Math. Phys. 356 (2017)) and Moinat–Weber, *Space-time localisation for
the dynamic Φ⁴₃ model* (Comm. Pure Appl. Math. 73 (2020)). The proof is
`GlobalPhi43.globalDynamics`.
-/

public section

namespace GlobalPhi43.Statements

open MeasureTheory Set
open scoped NNReal
open RegularityStructures

/-- **Global dynamics of the Φ⁴₃ equation.** For every mass `a` and exponent
`η ∈ (-2/3, -1/2)` there is a constant profile `K_{a,η} : [1, ∞) → [0, ∞)` (for (B4)), chosen before
the noise space, such that for every admissible noise space (a space-time white noise `W` on a
complete probability space) there are an event `Ω₀` of probability one, a flow `u(t,s;x)` on `𝒞^η`
and a probability measure `μ` on `𝒞^η` with the clauses (B1)–(B8): a continuous measurable flow,
adapted to the noise windows, consistent with Theorem A, coming down from infinity,
time-homogeneous, Feller Markov, with `μ` an invariant measure obtained by Krylov–Bogoliubov and the
law of a stationary solution. -/
theorem globalDynamics :
    ∀ (a : ℝ) (η : NegExponent) (hη : (η : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ))),
    ∃ K : ℝ → ℝ≥0,
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
      (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W),
    ∃ (Ω₀ : Set Ω) (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η) (μ : Measure (HolderBesov η)),
      GlobalPhi43.IsGlobalPhi43Flow K P W a η Ω₀ u μ :=
  by exact GlobalPhi43.globalDynamics

end GlobalPhi43.Statements

end
