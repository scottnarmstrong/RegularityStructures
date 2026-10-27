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
public import GlobalPhi43Statements.Defs.NoiseWindowSigma

/-!
# `GlobalPhi43.IsWindowAdapted`

Clause (B2): adaptedness to the noise windows.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BoundedContinuousFunction

namespace GlobalPhi43

open RegularityStructures RegularityStructures.Phi43

variable {Ω : Type*} [MeasurableSpace Ω] {η : NegExponent}

/-- **(B2)** Adaptedness: `ω ↦ u(t,s;x)(ω)` is `𝓕_{s,t}`-measurable for `0 ≤ s ≤ t`. -/
def IsWindowAdapted (P : Measure Ω) (W : (SpaceTime → ℝ) → Ω → ℝ)
    (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η) : Prop :=
  ∀ s t, 0 ≤ s → s ≤ t → ∀ x, Measurable[noiseWindowSigma P W s t] fun ω => u t s x ω

end GlobalPhi43

end
