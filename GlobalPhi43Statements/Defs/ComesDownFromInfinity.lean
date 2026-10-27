/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Mollifier
public import Phi43.Constants
public import Phi43.ClassicalSolution
public import Phi43.Limit
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import GlobalPhi43Statements.Defs.WindowSup

/-!
# `GlobalPhi43.ComesDownFromInfinity`

Clause (B4): coming down from infinity.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BoundedContinuousFunction

namespace GlobalPhi43

open RegularityStructures RegularityStructures.Phi43

variable {Ω : Type*} [MeasurableSpace Ω] {η : NegExponent}

/-- **(B4)** Coming down from infinity, with the constant profile `K : [1, ∞) → [0, ∞)`: for every
`s ≥ 0` the all-data window supremum `S_s = windowSup u s` is `𝓕`-measurable, and
`𝔼[S_s^p] ≤ K p` for every `p ≥ 1` (extended expectation). -/
def ComesDownFromInfinity (P : Measure Ω) (K : ℝ → ℝ≥0)
    (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η) : Prop :=
  ∀ s, 0 ≤ s → Measurable (windowSup u s) ∧
    ∀ p : ℝ, 1 ≤ p → ∫⁻ ω, windowSup u s ω ^ p ∂P ≤ K p

end GlobalPhi43

end
