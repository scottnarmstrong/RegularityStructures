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
public import GlobalPhi43Statements.Defs.IsContinuousMeasurableFlow
public import GlobalPhi43Statements.Defs.IsWindowAdapted
public import GlobalPhi43Statements.Defs.IsConsistentWithTheoremA
public import GlobalPhi43Statements.Defs.ComesDownFromInfinity
public import GlobalPhi43Statements.Defs.IsTimeHomogeneous
public import GlobalPhi43Statements.Defs.IsFellerMarkovFlow
public import GlobalPhi43Statements.Defs.IsKrylovBogoliubovInvariant
public import GlobalPhi43Statements.Defs.IsStationarySolution

/-!
# `GlobalPhi43.IsGlobalPhi43Flow`

The conclusion of the global dynamics: (B1)–(B8) for the witnesses `(Ω₀, u, μ)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BoundedContinuousFunction

namespace GlobalPhi43

open RegularityStructures RegularityStructures.Phi43

variable {Ω : Type*} [MeasurableSpace Ω] {η : NegExponent}

/-- The conclusion of `GlobalPhi43.Statements.globalDynamics` for the witnesses `(Ω₀, u, μ)`: `Ω₀` is an event of probability one,
and (B1)–(B8) hold, with the constant profile `K` in (B4) and the one probability measure `μ`
witnessing both (B7) and (B8). -/
def IsGlobalPhi43Flow (K : ℝ → ℝ≥0) (P : Measure Ω) (W : (SpaceTime → ℝ) → Ω → ℝ) (a : ℝ)
    (η : NegExponent) (Ω₀ : Set Ω) (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η)
    (μ : Measure (HolderBesov η)) : Prop :=
  MeasurableSet Ω₀ ∧ P Ω₀ = 1 ∧
    IsContinuousMeasurableFlow Ω₀ u ∧
    IsWindowAdapted P W u ∧
    IsConsistentWithTheoremA P W a η u ∧
    ComesDownFromInfinity P K u ∧
    IsTimeHomogeneous P u ∧
    IsFellerMarkovFlow P W u ∧
    IsProbabilityMeasure μ ∧ IsKrylovBogoliubovInvariant P u μ ∧ IsStationarySolution P W u μ

end GlobalPhi43

end
