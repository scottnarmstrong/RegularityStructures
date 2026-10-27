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

/-!
# `GlobalPhi43.IsTimeHomogeneous`

Clause (B5): time homogeneity.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BoundedContinuousFunction

namespace GlobalPhi43

open RegularityStructures RegularityStructures.Phi43

variable {Ω : Type*} [MeasurableSpace Ω] {η : NegExponent}

/-- **(B5)** Time homogeneity: for `s ≥ 0`, `k ≥ 1`, times `tᵢ ≥ 0` and data `xᵢ`, the
`(𝒞^η)^k`-valued vectors `(u(s+tᵢ,s;xᵢ))ᵢ` and `(u(tᵢ,0;xᵢ))ᵢ` have the same law. -/
def IsTimeHomogeneous (P : Measure Ω) (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η) : Prop :=
  ∀ s, 0 ≤ s → ∀ (k : ℕ), 1 ≤ k → ∀ (t : Fin k → ℝ), (∀ i, 0 ≤ t i) → ∀ x : Fin k → HolderBesov η,
    P.map (fun ω i => u (s + t i) s (x i) ω) = P.map fun ω i => u (t i) 0 (x i) ω

end GlobalPhi43

end
