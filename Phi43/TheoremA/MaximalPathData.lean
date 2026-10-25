/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.TheoremA.SequencePaths
public import Mathlib.Order.CompletePartialOrder

/-!
# The measurable maximal-path data

This module fixes the countable event family used by the Theorem A assembly.  The event at a
positive rational time records both a uniform Holder--Besov bound and a uniform Cauchy condition
for the selected smooth approximations.  The resulting explosion-time candidate is measurable by
countable unions and suprema; no measurability of model distances is used.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures.Phi43

variable {Ω : Type*} [MeasurableSpace Ω] {η : NegExponent}

local instance assemblyPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- A selected family is uniformly controlled through the rational time `q` at level `L`. -/
@[expose] noncomputable def assemblyPathEvent (q : ℚ) (L : ℕ) (x : ℕ → Ω → ℝ → HolderBesov η)
    (hcont : ∀ n ω, ContinuousOn (x n ω) (Ici (0 : ℝ))) (ω : Ω) : Prop :=
  0 < (q : ℝ) ∧
    (∀ n, ‖assemblyPathRestriction q x hcont n ω‖ ≤ (L : ℝ)) ∧
      CauchySeq (fun n => assemblyPathRestriction q x hcont n ω)

omit [MeasurableSpace Ω] in
theorem assemblyPathEvent_cauchy (q : ℚ) (L : ℕ) (x : ℕ → Ω → ℝ → HolderBesov η)
    (hcont : ∀ n ω, ContinuousOn (x n ω) (Ici (0 : ℝ))) (ω : Ω)
    (hA : assemblyPathEvent q L x hcont ω) :
    CauchySeq (fun n => assemblyPathRestriction q x hcont n ω) := by
  exact hA.2.2

theorem assemblyPathEvent_measurableSet (q : ℚ) (L : ℕ) (x : ℕ → Ω → ℝ → HolderBesov η)
    (hcont : ∀ n ω, ContinuousOn (x n ω) (Ici (0 : ℝ)))
    (hmeas : ∀ n t, 0 ≤ t → Measurable (fun ω => x n ω t)) :
    MeasurableSet {ω | assemblyPathEvent q L x hcont ω} := by
  by_cases hq : 0 < (q : ℝ)
  · simp only [assemblyPathEvent, hq, true_and]
    exact (assemblyPathUniformBound_measurableSet q x hcont hmeas (L : ℝ)).inter
      (assemblyPathCauchy_measurableSet q x hcont hmeas)
  · simp only [assemblyPathEvent, hq, false_and]
    exact MeasurableSet.empty

/-- The maximal time associated with the selected path events. -/
noncomputable def assemblyTau (x : ℕ → Ω → ℝ → HolderBesov η)
    (hcont : ∀ n ω, ContinuousOn (x n ω) (Ici (0 : ℝ))) (ω : Ω) : ℝ≥0∞ := by
  classical
  exact if ∃ q : ℚ, ∃ L : ℕ, assemblyPathEvent q L x hcont ω then
    ⨆ q : ℚ, ⨆ L : ℕ,
      if assemblyPathEvent q L x hcont ω then ENNReal.ofReal (q : ℝ) else 0
  else ⊤

omit [MeasurableSpace Ω] in
theorem assemblyTau_eq (x : ℕ → Ω → ℝ → HolderBesov η)
    (hcont : ∀ n ω, ContinuousOn (x n ω) (Ici (0 : ℝ))) (ω : Ω) :
    assemblyTau x hcont ω =
      if ∃ q : ℚ, ∃ L : ℕ, assemblyPathEvent q L x hcont ω then
        ⨆ q : ℚ, ⨆ L : ℕ,
          if assemblyPathEvent q L x hcont ω then ENNReal.ofReal (q : ℝ) else 0
      else ⊤ := by
  classical
  rfl

end RegularityStructures.Phi43

end
