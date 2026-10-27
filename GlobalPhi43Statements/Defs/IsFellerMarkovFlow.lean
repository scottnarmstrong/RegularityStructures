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
public import GlobalPhi43Statements.Defs.FlowLaw
public import GlobalPhi43Statements.Defs.FlowTransition

/-!
# `GlobalPhi43.IsFellerMarkovFlow`

Clause (B6): Feller Markov process.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BoundedContinuousFunction

namespace GlobalPhi43

open RegularityStructures RegularityStructures.Phi43

variable {Ω : Type*} [MeasurableSpace Ω] {η : NegExponent}

/-- **(B6)** Feller Markov process for `P_t(x, A) = P(u(t,0;x) ∈ A)`: probability kernels, jointly
measurable in `(t, x)`, `P_0(x, ·) = δ_x`, `P_{t+s} = P_t P_s`; the Markov property
`𝔼[f(u(s+t,0;x)) | 𝓕_s] = (P_t f)(u(s,0;x))` a.s. for bounded measurable `f`; and the Feller
property: `P_t f` is bounded and continuous for bounded continuous `f`, and `t ↦ (P_t f)(x)` is
continuous. -/
def IsFellerMarkovFlow (P : Measure Ω) (W : (SpaceTime → ℝ) → Ω → ℝ)
    (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η) : Prop :=
  (∀ t, 0 ≤ t → ∀ x, IsProbabilityMeasure (flowLaw P u t x)) ∧
    (∀ A : Set (HolderBesov η), MeasurableSet A →
      Measurable fun p : Ici (0 : ℝ) × HolderBesov η => flowLaw P u p.1 p.2 A) ∧
    (∀ x, flowLaw P u 0 x = Measure.dirac x) ∧
    (∀ s t, 0 ≤ s → 0 ≤ t → ∀ x, ∀ A : Set (HolderBesov η), MeasurableSet A →
      flowLaw P u (t + s) x A = ∫⁻ y, flowLaw P u s y A ∂flowLaw P u t x) ∧
    (∀ f : HolderBesov η → ℝ, Measurable f → (∃ M, ∀ y, |f y| ≤ M) →
      ∀ s t, 0 ≤ s → 0 ≤ t → ∀ x,
        P[fun ω => f (u (s + t) 0 x ω) | noiseWindowSigma P W 0 s] =ᵐ[P]
          fun ω => flowTransition P u t f (u s 0 x ω)) ∧
    ∀ f : HolderBesov η →ᵇ ℝ,
      (∀ t, 0 ≤ t → Continuous (flowTransition P u t f) ∧
        ∃ M, ∀ x, |flowTransition P u t f x| ≤ M) ∧
      ∀ x, ContinuousOn (fun t => flowTransition P u t f x) (Ici 0)

end GlobalPhi43

end
