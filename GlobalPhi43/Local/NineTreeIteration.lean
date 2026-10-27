/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.LocalIteration
public import GlobalPhi43.Local.TreeIndex

/-! The named nine-tree interface of the augmented local iteration. B_tau
still denotes the numerical value to be supplied by the actual seminorm
construction; this module does not identify arbitrary B with kernel tests. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures Set MW20
open scoped ContDiff

/-- The exact finite maximum of the nine source tree roots. -/
@[expose] def nineTreeScale (κ : ℝ) (B : LocalTree → ℝ) : ℝ :=
  treeRadiusMajorant B (fun τ : LocalTree => τ.degree κ) 1

/-- Local-carrier, nine-tree version of the augmented iteration. The one
constant is selected before u,J, all nine norm values, defects and R.
The seminorm construction and the PDE estimate `RadiusInteriorRow`
are explicit assumptions. -/
theorem nine_tree_remainder_iteration {κ C c : ℝ}
    (hκ : κ ∈ Ioo (0 : ℝ) (1 / 14))
    (hC : 1 ≤ C) (hc : 0 < c) (hc₁ : c ≤ 1) :
    ∃ K > 0, ∀ (u J : ParabolicSpace → ℝ),
      (∃ O : Set ParabolicSpace, IsOpen O ∧ closure (sourceCylinder 0) ⊆ O ∧
        ContDiffOn ℝ ∞ u O) → ContDiff ℝ ∞ J →
      ∀ (B : LocalTree → ℝ), (∀ τ, 0 ≤ B τ) → ∀ E₁ E₂ E₃,
      0 ≤ E₁ → 0 ≤ E₂ → 0 ≤ E₃ →
      RadiusInteriorRow (fun z => u z - J z) B (fun τ : LocalTree => τ.degree κ) C c E₁ E₂ E₃ →
      ∀ R ∈ Ioo (0 : ℝ) 1, ∀ z ∈ sourceCylinder R, |u z - J z| ≤
        K * max (1 / R) (max (nineTreeScale κ B) (defectScale E₁ E₂ E₃)) := by
  have hp (τ : LocalTree) : 0 < τ.degree κ := τ.degree_pos (by linarith [hκ.2])
  obtain ⟨K, hK, hb⟩ := local_remainder_radius_iteration (fun τ : LocalTree => τ.degree κ)
    hC hc hc₁ hp
  exact ⟨K, hK, hb⟩

end GlobalPhi43.Local
