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
public import GlobalPhi43Statements.Defs.FlowLaw
public import GlobalPhi43Statements.Defs.AveragedLaw
public import GlobalPhi43Statements.Defs.ExtNorm

/-!
# `GlobalPhi43.IsKrylovBogoliubovInvariant`

Clause (B7): the invariant measure.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BoundedContinuousFunction

namespace GlobalPhi43

open RegularityStructures RegularityStructures.Phi43

variable {Ω : Type*} [MeasurableSpace Ω] {η : NegExponent}

/-- **(B7)** for a probability measure `μ` on `𝒞^η`: (i) `μ P_t = μ` for `t ≥ 0`; (ii) `μ` is the
weak limit of `ν_{T_k}` along some `T_k > 0`, `T_k → ∞`; (iii) `∫ 𝒩_{η'}^p dμ < ∞` for `p ≥ 1` and
`η' ∈ [η, -1/2)`. -/
def IsKrylovBogoliubovInvariant (P : Measure Ω) (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η)
    (μ : Measure (HolderBesov η)) : Prop :=
  (∀ t, 0 ≤ t → ∀ A : Set (HolderBesov η), MeasurableSet A →
      ∫⁻ x, flowLaw P u t x A ∂μ = μ A) ∧
    (∃ T : ℕ → ℝ, (∀ k, 0 < T k) ∧ Tendsto T atTop atTop ∧
      ∀ f : HolderBesov η →ᵇ ℝ,
        Tendsto (fun k => ∫ z, f z ∂averagedLaw P u (T k)) atTop (𝓝 (∫ z, f z ∂μ))) ∧
    ∀ p : ℝ, 1 ≤ p → ∀ η' : ℝ, (η : ℝ) ≤ η' → η' < -(1 / 2) →
      ∫⁻ z, extNorm η η' z ^ p ∂μ < ⊤

end GlobalPhi43

end
