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
# `GlobalPhi43.IsContinuousMeasurableFlow`

Clause (B1): continuous measurable flow.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BoundedContinuousFunction

namespace GlobalPhi43

open RegularityStructures RegularityStructures.Phi43

variable {Ω : Type*} [MeasurableSpace Ω] {η : NegExponent}

/-- **(B1)** Continuous measurable flow: `u` is jointly measurable on
`{(t,s) : 0 ≤ s ≤ t} × 𝒞^η × Ω`; it is the identity off `Ω₀`; for every `ω` and `s ≥ 0`,
`(t, x) ↦ u(t,s;x)(ω)` is continuous on `[s, ∞) × 𝒞^η`; `u(s,s;x) = x`; and
`u(r,s; u(s,t;x)) = u(r,t;x)` for `t ≤ s ≤ r`. -/
def IsContinuousMeasurableFlow (Ω₀ : Set Ω) (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η) :
    Prop :=
  Measurable (fun q : {p : ℝ × ℝ // 0 ≤ p.2 ∧ p.2 ≤ p.1} × HolderBesov η × Ω =>
      u q.1.1.1 q.1.1.2 q.2.1 q.2.2) ∧
    (∀ ω ∉ Ω₀, ∀ t s, 0 ≤ s → s ≤ t → ∀ x, u t s x ω = x) ∧
    (∀ ω, ∀ s, 0 ≤ s → Continuous fun p : Ici s × HolderBesov η => u p.1 s p.2 ω) ∧
    (∀ s, 0 ≤ s → ∀ x ω, u s s x ω = x) ∧
    ∀ t s r, 0 ≤ t → t ≤ s → s ≤ r → ∀ x ω, u r s (u s t x ω) ω = u r t x ω

end GlobalPhi43

end
