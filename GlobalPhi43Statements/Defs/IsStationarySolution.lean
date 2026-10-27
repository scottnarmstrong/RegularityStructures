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
# `GlobalPhi43.IsStationarySolution`

Clause (B8): the stationary solution.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BoundedContinuousFunction

namespace GlobalPhi43

open RegularityStructures RegularityStructures.Phi43

variable {Ω : Type*} [MeasurableSpace Ω] {η : NegExponent}

/-- **(B8)** Stationary solution, on `(Ω × 𝒞^η, 𝓕 ⊗ 𝓑(𝒞^η), P ⊗ μ)`: the process
`ũ(t)(ω, z) = u(t,0;z)(ω)` has finite-dimensional distributions invariant under time shifts and
law `μ` at every `t ≥ 0`; `(ω, z) ↦ W(h)(ω)` is a white noise, independent of the initial field
`(ω, z) ↦ z`, which has law `μ`. -/
def IsStationarySolution (P : Measure Ω) (W : (SpaceTime → ℝ) → Ω → ℝ)
    (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η) (μ : Measure (HolderBesov η)) : Prop :=
  (∀ (k : ℕ) (t : Fin k → ℝ), (∀ i, 0 ≤ t i) → ∀ r, 0 ≤ r →
      (P.prod μ).map (fun q i => u (t i + r) 0 q.2 q.1) =
        (P.prod μ).map fun q i => u (t i) 0 q.2 q.1) ∧
    (∀ t, 0 ≤ t → (P.prod μ).map (fun q => u t 0 q.2 q.1) = μ) ∧
    IsWhiteNoise (P.prod μ) (fun h q => W h q.1) ∧
    (P.prod μ).map Prod.snd = μ ∧
    Indep (⨆ (h : SpaceTime → ℝ) (_ : MemLp h 2),
        MeasurableSpace.comap (fun q : Ω × HolderBesov η => W h q.1) inferInstance)
      (MeasurableSpace.comap Prod.snd inferInstance) (P.prod μ)

end GlobalPhi43

end
