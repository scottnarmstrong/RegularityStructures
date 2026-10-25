/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.TheoremA.BoundedTau
public import Phi43.TheoremA.MaximalPathData

/-!
# Measurable closure of bounded lifetime events

The bounded lifetime is defined from rational uniform bounds, while the stopped-limit package
needs compact-window Cauchy data.  This module records the measurable event on which every bounded
rational window also has the maximal-path Cauchy property.  The selected path is retained on that
event and totalised by a fixed value otherwise.
-/

public section

noncomputable section

open MeasureTheory Set

namespace RegularityStructures.Phi43

@[expose] def assemblyBoundedTauClosureEvent
    {Ω : Type*} {η : NegExponent}
    (x : ℕ → Ω → ℝ → HolderBesov η)
    (hcont : ∀ n ω, ContinuousOn (x n ω) (Ici (0 : ℝ))) (ω : Ω) : Prop :=
  (∃ q : ℚ, ∃ L : ℕ,
      assemblyRationalBoundedPathEvent q L x hcont ω) ∧
    ∀ q : ℚ, ∀ L : ℕ,
      assemblyRationalBoundedPathEvent q L x hcont ω →
        assemblyPathEvent q L x hcont ω

theorem assemblyBoundedTauClosureEvent_measurableSet
    {Ω : Type*} [MeasurableSpace Ω] {η : NegExponent}
    (x : ℕ → Ω → ℝ → HolderBesov η)
    (hcont : ∀ n ω, ContinuousOn (x n ω) (Ici (0 : ℝ)))
    (hmeas : ∀ n t, 0 ≤ t → Measurable (fun ω => x n ω t)) :
    MeasurableSet {ω | assemblyBoundedTauClosureEvent x hcont ω} := by
  have hbounded : MeasurableSet {ω | ∃ q : ℚ, ∃ L : ℕ,
      assemblyRationalBoundedPathEvent q L x hcont ω} := by
    rw [show {ω | ∃ q : ℚ, ∃ L : ℕ,
        assemblyRationalBoundedPathEvent q L x hcont ω} =
      ⋃ q : ℚ, ⋃ L : ℕ,
        {ω | assemblyRationalBoundedPathEvent q L x hcont ω} by
      ext ω
      simp]
    exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun L =>
      assemblyRationalBoundedPathEvent_measurableSet q L x hcont hmeas
  have hclosed : MeasurableSet {ω | ∀ q : ℚ, ∀ L : ℕ,
      assemblyRationalBoundedPathEvent q L x hcont ω →
        assemblyPathEvent q L x hcont ω} := by
    rw [show {ω | ∀ q : ℚ, ∀ L : ℕ,
        assemblyRationalBoundedPathEvent q L x hcont ω →
          assemblyPathEvent q L x hcont ω} =
      ⋂ q : ℚ, ⋂ L : ℕ,
        ({ω | assemblyRationalBoundedPathEvent q L x hcont ω}ᶜ ∪
          {ω | assemblyPathEvent q L x hcont ω}) by
      ext ω
      simp only [Set.mem_iInter, Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq,
        imp_iff_not_or]]
    exact MeasurableSet.iInter fun q => MeasurableSet.iInter fun L =>
      (assemblyRationalBoundedPathEvent_measurableSet q L x hcont hmeas).compl.union
        (assemblyPathEvent_measurableSet q L x hcont hmeas)
  rw [show {ω | assemblyBoundedTauClosureEvent x hcont ω} =
      {ω | ∃ q : ℚ, ∃ L : ℕ,
        assemblyRationalBoundedPathEvent q L x hcont ω} ∩
      {ω | ∀ q : ℚ, ∀ L : ℕ,
        assemblyRationalBoundedPathEvent q L x hcont ω →
          assemblyPathEvent q L x hcont ω} by
    ext ω
    rfl]
  exact hbounded.inter hclosed

@[expose] noncomputable def assemblyBoundedTauClosurePath
    {Ω : Type*} {η : NegExponent}
    (x : ℕ → Ω → ℝ → HolderBesov η)
    (hcont : ∀ n ω, ContinuousOn (x n ω) (Ici (0 : ℝ)))
    (x₀ : HolderBesov η) : ℕ → Ω → ℝ → HolderBesov η := by
  classical
  exact fun n ω t => if assemblyBoundedTauClosureEvent x hcont ω then
    x n ω t else x₀

theorem assemblyBoundedTauClosurePath_continuousOn
    {Ω : Type*} {η : NegExponent}
    (x : ℕ → Ω → ℝ → HolderBesov η)
    (hcont : ∀ n ω, ContinuousOn (x n ω) (Ici (0 : ℝ)))
    (x₀ : HolderBesov η) :
    ∀ n ω, ContinuousOn
      (assemblyBoundedTauClosurePath x hcont x₀ n ω) (Ici (0 : ℝ)) := by
  classical
  intro n ω
  change ContinuousOn (fun t : ℝ =>
    if assemblyBoundedTauClosureEvent x hcont ω then x n ω t else x₀)
    (Ici (0 : ℝ))
  split
  · exact hcont n ω
  · exact continuousOn_const

theorem assemblyBoundedTauClosurePath_measurable
    {Ω : Type*} [MeasurableSpace Ω] {η : NegExponent}
    (x : ℕ → Ω → ℝ → HolderBesov η)
    (hcont : ∀ n ω, ContinuousOn (x n ω) (Ici (0 : ℝ)))
    (x₀ : HolderBesov η)
    (hmeas : ∀ n t, 0 ≤ t → Measurable (fun ω => x n ω t)) :
    ∀ n t, 0 ≤ t → Measurable
      (fun ω => assemblyBoundedTauClosurePath x hcont x₀ n ω t) := by
  classical
  have hE := assemblyBoundedTauClosureEvent_measurableSet x hcont hmeas
  intro n t ht
  change Measurable (fun ω =>
    if assemblyBoundedTauClosureEvent x hcont ω then x n ω t else x₀)
  exact Measurable.ite hE (hmeas n t ht) measurable_const

end RegularityStructures.Phi43

end
