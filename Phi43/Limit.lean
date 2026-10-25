/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HolderBesov
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# The limit conditions (A1)–(A3)

Conditions (A1)–(A3) of Theorem A of the statement. Given solutions `u ε ω` of the regularised
equations, a pair `(τ, v)` is a limit if
* (A1) `τ` is a positive random time, each path `v ω` is continuous on `[0, τ ω)` with
  `v ω 0 = u₀`, and `ω ↦ v ω t` is measurable on `{τ > t}`;
* (A2) `τ` is the explosion time: if `τ ω < ∞` then `‖v ω t‖_η` is unbounded on `[0, τ ω)`;
* (A3) for all `T, δ > 0`, `P(τ > T and sup_{t ≤ T} ‖u_ε(t) - v(t)‖_η > δ) → 0` as `ε ↓ 0`.

Source: the statement, Theorem A.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace RegularityStructures.Phi43

/-- `(τ, v)` satisfies conditions (A1)–(A3) of Theorem A for the solutions `u` and data `u₀`. -/
structure IsPhi43Limit {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (η : NegExponent)
    (u₀ : C(Torus3, ℝ)) (u : ℝ → Ω → ℝ → C(Torus3, ℝ)) (τ : Ω → ℝ≥0∞)
    (v : Ω → ℝ → HolderBesov η) : Prop where
  measurable_τ : Measurable τ
  τ_pos : ∀ ω, 0 < τ ω
  continuousOn : ∀ ω, ContinuousOn (v ω) {t | 0 ≤ t ∧ ENNReal.ofReal t < τ ω}
  initial : ∀ ω, v ω 0 = toHolderBesov η u₀
  measurable : ∀ t, 0 ≤ t → ∀ s : Set (HolderBesov η), MeasurableSet s →
    MeasurableSet {ω | ENNReal.ofReal t < τ ω ∧ v ω t ∈ s}
  explosion : ∀ ω, τ ω < ⊤ →
    ¬ BddAbove ((fun t => ‖v ω t‖) '' {t | 0 ≤ t ∧ ENNReal.ofReal t < τ ω})
  converges : ∀ T, 0 < T → ∀ δ, 0 < δ →
    Tendsto (fun ε => P {ω | ENNReal.ofReal T < τ ω ∧
      ∃ t ∈ Set.Icc 0 T, δ < ‖toHolderBesov η (u ε ω t) - v ω t‖}) (𝓝[>] 0) (𝓝 0)

end RegularityStructures.Phi43

end
