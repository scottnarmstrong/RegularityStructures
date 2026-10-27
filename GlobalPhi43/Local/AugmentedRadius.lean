/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.DefectScale
public import GlobalPhi43.MW20.RadiusUniform

/-! Radius iteration with both source trees and the local smooth defects.
The analytic interior row remains an explicit input of this iteration component.
It is not asserted as an added hypothesis of the final local-data theorem. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures Set MW20

/-- The source and defect tests use one fixed common smallness constant. -/
@[expose] def AugmentedSmall {I : Type*} (B p : I → ℝ)
    (c M E₁ E₂ E₃ : ℝ) : Prop :=
  (∀ i, B i ≤ c * M ^ p i) ∧ DefectSmall c M E₁ E₂ E₃

/-- Failure of the augmented tests controls the actual cylinder mass. -/
theorem augmented_stopping_bound {I : Type*} [Fintype I] [Nonempty I]
    (B p : I → ℝ) {c M E₁ E₂ E₃ : ℝ}
    (hc : 0 < c) (hc₁ : c ≤ 1) (hM : 0 ≤ M)
    (hB : ∀ i, 0 ≤ B i) (hp : ∀ i, 0 < p i)
    (h₁ : 0 ≤ E₁) (h₂ : 0 ≤ E₂) (h₃ : 0 ≤ E₃)
    (hfail : ¬ AugmentedSmall B p c M E₁ E₂ E₃) :
    M ≤ max (treeRadiusMajorant B p c) ((2 / c) * defectScale E₁ E₂ E₃) := by
  by_cases ht : ∀ i, B i ≤ c * M ^ p i
  · have hd : ¬ DefectSmall c M E₁ E₂ E₃ := fun hd => hfail ⟨ht, hd⟩
    exact (mass_bound_of_defect_scale_failure hc hc₁ hM h₁ h₂ h₃ hd).trans
      (le_max_right _ _)
  · exact (mass_bound_of_not_small B p hM hc hB hp
      (tree_contribution_le_majorant B p c) ht).trans (le_max_left _ _)

end GlobalPhi43.Local
