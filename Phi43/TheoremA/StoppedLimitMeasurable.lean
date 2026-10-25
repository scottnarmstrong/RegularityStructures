/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HolderBesov
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.MetricSpace.Cauchy

/-!
# Measurable stopped pointwise limits

The lifetime construction uses a pointwise limit only on the active set
`{ω | 0 ≤ t ∧ ofReal t < τ ω}` and a fixed zero value elsewhere.  This module
packages that choice and its measurability from measurable approximants.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace RegularityStructures.Phi43

def assemblyStoppedLimit
    {Ω : Type*} {η : NegExponent}
    (x : ℕ → Ω → ℝ → HolderBesov η)
    (τ : Ω → ℝ≥0∞)
    (hCauchy : ∀ ω t, 0 ≤ t → ENNReal.ofReal t < τ ω →
      CauchySeq (fun n => x n ω t)) :
    Ω → ℝ → HolderBesov η :=
  fun ω t => if h : 0 ≤ t ∧ ENNReal.ofReal t < τ ω then
    Classical.choose (cauchySeq_tendsto_of_complete (hCauchy ω t h.1 h.2)) else 0

end RegularityStructures.Phi43

end

public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace RegularityStructures.Phi43

theorem assemblyStoppedLimit_measurable
    {Ω : Type*} [MeasurableSpace Ω] {η : NegExponent}
    (x : ℕ → Ω → ℝ → HolderBesov η)
    (τ : Ω → ℝ≥0∞)
    (hCauchy : ∀ ω t, 0 ≤ t → ENNReal.ofReal t < τ ω →
      CauchySeq (fun n => x n ω t))
    (hτ : Measurable τ)
    (hmeas : ∀ n t, 0 ≤ t → Measurable (fun ω => x n ω t))
    {t : ℝ} (ht : 0 ≤ t) :
    Measurable (fun ω => assemblyStoppedLimit x τ hCauchy ω t) := by
  let A : Set Ω := {ω | ENNReal.ofReal t < τ ω}
  have hA : MeasurableSet A := by
    dsimp [A]
    exact measurableSet_lt measurable_const hτ
  have hf : ∀ n : ℕ, Measurable (fun ω =>
      if ω ∈ A then x n ω t else 0) := by
    intro n
    exact Measurable.ite hA (hmeas n t ht) measurable_const
  have hlim_point : ∀ ω, Tendsto (fun n => if ω ∈ A then x n ω t else 0) atTop
      (𝓝 (assemblyStoppedLimit x τ hCauchy ω t)) := by
    intro ω
    by_cases hω : ω ∈ A
    · have hω' : ENNReal.ofReal t < τ ω := by simpa [A] using hω
      have hact : 0 ≤ t ∧ ENNReal.ofReal t < τ ω := ⟨ht, hω'⟩
      simpa only [assemblyStoppedLimit, hω, ite_true, dite_eq_left hact] using
        (Classical.choose_spec
          (cauchySeq_tendsto_of_complete (hCauchy ω t ht hω')))
    · have hnot : ¬ (0 ≤ t ∧ ENNReal.ofReal t < τ ω) := by
        intro h
        exact hω (by simpa [A] using h.2)
      simp only [assemblyStoppedLimit, hω, ite_false, dite_eq_right hnot]
      exact tendsto_const_nhds
  have hlim : Tendsto (fun n ω => if ω ∈ A then x n ω t else 0) atTop
      (𝓝 (fun ω => assemblyStoppedLimit x τ hCauchy ω t)) := by
    rw [tendsto_pi_nhds]
    exact hlim_point
  exact measurable_of_tendsto_metrizable hf hlim

end RegularityStructures.Phi43

end
