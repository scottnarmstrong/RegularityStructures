/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.NineTreeIteration

/-! The literal cylinder supremum conclusion on the complete target radius
range, with the same constant as the pointwise iteration. -/
public section

namespace GlobalPhi43.Local

open RegularityStructures Set MW20
open scoped ContDiff

theorem sourceCylinder_nonempty_unit {R : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1) :
    (sourceCylinder R).Nonempty := by
  refine ⟨((R ^ 2 + 1) / 2, 0), ?_⟩
  change R ^ 2 < (R ^ 2 + 1) / 2 ∧ (R ^ 2 + 1) / 2 < 1 ∧
    ∀ i : Fin 3, |(0 : ℝ)| < 1 - R
  have hsq : R ^ 2 < 1 := by nlinarith [hR.1, hR.2]
  refine ⟨by linarith, by linarith, ?_⟩
  intro i
  simpa only [abs_zero] using sub_pos.mpr hR.2

theorem sourceSup_le_of_pointwise_unit (v : ParabolicSpace → ℝ)
    {R A : ℝ} (hR : R ∈ Ioo (0 : ℝ) 1)
    (hb : ∀ z ∈ sourceCylinder R, |v z| ≤ A) : sourceSup v R ≤ A := by
  apply csSup_le ((sourceCylinder_nonempty_unit hR).image _)
  rintro a ⟨z, hz, rfl⟩
  exact hb z hz

/-- The nine-tree conditional iteration exports the literal sup norm on P_R.
Only local smoothness of u near P-bar is used, and K precedes all data. -/
theorem nine_tree_remainder_sup_iteration {κ C c : ℝ}
    (hκ : κ ∈ Ioo (0 : ℝ) (1 / 14))
    (hC : 1 ≤ C) (hc : 0 < c) (hc₁ : c ≤ 1) :
    ∃ K > 0, ∀ (u J : ParabolicSpace → ℝ),
      (∃ O : Set ParabolicSpace, IsOpen O ∧ closure (sourceCylinder 0) ⊆ O ∧
        ContDiffOn ℝ ∞ u O) → ContDiff ℝ ∞ J →
      ∀ (B : LocalTree → ℝ), (∀ τ, 0 ≤ B τ) → ∀ E₁ E₂ E₃,
      0 ≤ E₁ → 0 ≤ E₂ → 0 ≤ E₃ →
      RadiusInteriorRow (fun z => u z - J z) B (fun τ : LocalTree => τ.degree κ)
        C c E₁ E₂ E₃ →
      ∀ R ∈ Ioo (0 : ℝ) 1, sourceSup (fun z => u z - J z) R ≤
        K * max (1 / R) (max (nineTreeScale κ B) (defectScale E₁ E₂ E₃)) := by
  obtain ⟨K, hK, hb⟩ := nine_tree_remainder_iteration hκ hC hc hc₁
  refine ⟨K, hK, ?_⟩
  intro u J hu hJ B hB E₁ E₂ E₃ h₁ h₂ h₃ hmax R hR
  exact sourceSup_le_of_pointwise_unit _ hR
    (hb u J hu hJ B hB E₁ E₂ E₃ h₁ h₂ h₃ hmax R hR)

end GlobalPhi43.Local
