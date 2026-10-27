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
# `GlobalPhi43.IsConsistentWithTheoremA`

Clause (B3): consistency with Theorem A.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BoundedContinuousFunction

namespace GlobalPhi43

open RegularityStructures RegularityStructures.Phi43

variable {Ω : Type*} [MeasurableSpace Ω] {η : NegExponent}

/-- **(B3)** Consistency with Theorem A: for every mollifier `ρ`, regularised noises `ξ_ε` driven by
`W`, smooth `x` and classical solutions `u_ε` of the equation with counterterm
`a + 3C₁^ε - 9C₂^ε` and initial value `x`, `P(sup_{0≤t≤T} ‖u_ε(t) - u(t,0;x)‖_η > δ) → 0` as
`ε ↓ 0`, for all `T, δ > 0`; and the pair `(τ ≡ ∞, t ↦ u(t,0;x))` satisfies (A1)–(A3) of
Theorem A. -/
def IsConsistentWithTheoremA (P : Measure Ω) (W : (SpaceTime → ℝ) → Ω → ℝ) (a : ℝ) (η : NegExponent)
    (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η) : Prop :=
  ∀ (ρ : ℝ × (Fin 3 → ℝ) → ℝ), IsMollifier ρ →
  ∀ (ξ : ℝ → Ω → SpaceTime → ℝ), (∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε)) →
  ∀ (x : C(Torus3, ℝ)), IsSmoothOnTorus x →
  ∀ (uε : ℝ → Ω → ℝ → C(Torus3, ℝ)),
    (∀ ε ∈ Ioc (0 : ℝ) 1, ∀ ω, IsClassicalSolution
      (a + 3 * wickConstant ρ ε - 9 * sunsetConstant ρ ε) (ξ ε ω) x (uε ε ω)) →
    (∀ T, 0 < T → ∀ δ, 0 < δ →
      Tendsto (fun ε => P {ω | ∃ t ∈ Icc 0 T,
          δ < ‖toHolderBesov η (uε ε ω t) - u t 0 (toHolderBesov η x) ω‖})
        (𝓝[>] 0) (𝓝 0)) ∧
    IsPhi43Limit P η x uε (fun _ => ⊤) fun ω t => u t 0 (toHolderBesov η x) ω

end GlobalPhi43

end
