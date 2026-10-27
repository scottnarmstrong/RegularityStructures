/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.GenericNormalizedCaloricStep
public import GlobalPhi43.Local.ActualScaleRecurrence

/-! The normalized caloric data budget for the radius recurrence. -/
@[expose] public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 MeasureTheory Set
open scoped ContDiff ENNReal

 def genericCaloricDataBudget {I J : Type*} (A : Finset I) (α : I → ℝ)
    (B : Finset J) (β : J → ℝ) (γ C ε M₁ M₂ : ℝ) : ℝ :=
  C * M₁ * (∑ i ∈ A, ε ^ (2 * α i - 4 - γ)) +
    M₂ * ((∑ j ∈ B, ε ^ (γ - β j)) + C * (∑ j ∈ B, ε ^ (2 + γ - 2 * β j)))

end GlobalPhi43.Local
