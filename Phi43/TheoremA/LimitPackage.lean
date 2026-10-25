/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Limit
public import Phi43.TheoremA.StoppedLimitContinuity
public import Phi43.TheoremA.StoppedLimitInitial

/-!
# Packaging the stopped-limit fields

The measurable, continuous, explosive stopped limit used in the proof of Theorem A satisfies
`IsPhi43Limit` once its pointwise measurability, initial value, explosion,
and convergence fields have been supplied.  This is the form in which the limit enters the
proof of Theorem A.
-/

public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace RegularityStructures.Phi43

theorem assembly_isPhi43Limit_of_stoppedData
    {Ω : Type*} [MeasurableSpace Ω] {η : NegExponent}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (u₀ : C(Torus3, ℝ))
    (x : ℕ → Ω → ℝ → HolderBesov η)
    (u : ℝ → Ω → ℝ → C(Torus3, ℝ))
    (τ : Ω → ℝ≥0∞)
    (hCauchy : ∀ ω t, 0 ≤ t → ENNReal.ofReal t < τ ω →
      CauchySeq (fun n => x n ω t))
    (hcont : ∀ n ω, ContinuousOn (x n ω) (Ici (0 : ℝ)))
    (hmeas : ∀ n t, 0 ≤ t → Measurable (fun ω => x n ω t))
    (hwindow : ∀ ω T, 0 ≤ T → ENNReal.ofReal T < τ ω →
      CauchySeq (fun n =>
        ContinuousMap.mk (fun t : Icc (0 : ℝ) T => x n ω t.1)
          (continuousOn_iff_continuous_domRestrict.mp
            ((hcont n ω).mono Icc_subset_Ici_self))))
    (hτ : Measurable τ)
    (hτpos : ∀ ω, 0 < τ ω)
    (hinitial : ∀ n ω, x n ω 0 = toHolderBesov η u₀)
    (hexplosion : ∀ ω, τ ω < ⊤ →
      ¬ BddAbove ((fun t => ‖assemblyStoppedLimit x τ hCauchy ω t‖) ''
        {t | 0 ≤ t ∧ ENNReal.ofReal t < τ ω}))
    (hconverges : ∀ T, 0 < T → ∀ δ, 0 < δ →
      Tendsto (fun ε => P {ω | ENNReal.ofReal T < τ ω ∧
        ∃ t ∈ Icc (0 : ℝ) T,
          δ < ‖toHolderBesov η (u ε ω t) -
            assemblyStoppedLimit x τ hCauchy ω t‖})
        (𝓝[>] 0) (𝓝 0)) :
    IsPhi43Limit P η u₀ u τ (assemblyStoppedLimit x τ hCauchy) := by
  refine
    { measurable_τ := hτ
      τ_pos := hτpos
      continuousOn := assemblyStoppedLimit_continuousOn x τ hCauchy hcont hwindow
      initial := assemblyStoppedLimit_initial x τ (toHolderBesov η u₀)
        hCauchy hinitial hτpos
      measurable := ?_
      explosion := hexplosion
      converges := hconverges }
  intro t ht s hs
  have hvalue : Measurable (fun ω => assemblyStoppedLimit x τ hCauchy ω t) :=
    assemblyStoppedLimit_measurable x τ hCauchy hτ hmeas ht
  have hactive : MeasurableSet {ω | ENNReal.ofReal t < τ ω} :=
    measurableSet_lt measurable_const hτ
  have hvalue_set : MeasurableSet
      {ω | assemblyStoppedLimit x τ hCauchy ω t ∈ s} := hs.preimage hvalue
  rw [show {ω | ENNReal.ofReal t < τ ω ∧
      assemblyStoppedLimit x τ hCauchy ω t ∈ s} =
      {ω | ENNReal.ofReal t < τ ω} ∩
        {ω | assemblyStoppedLimit x τ hCauchy ω t ∈ s} by
    ext ω
    rfl]
  exact hactive.inter hvalue_set

end RegularityStructures.Phi43

end
