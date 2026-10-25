/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.FixedPointF.PlantData

/-!
# The enlarged group on the old symbols, and the enlarged product on old vectors

[Hai14, Definition 2.1, Definition 4.1]. Every element of `phi43ExtensionGroupF κ` acts on the old
symbols through the *same* parameter `p : G` of the old group
(`phi43ExtensionGroupF_old_params`), and the enlarged product of old-embedded vectors is the
embedding of the old product (`phi43ProductLinearF_oldEmb`).
-/

public section

namespace RegularityStructures.Phi43

theorem phi43ExtensionGroupF_old_params (κ : Kappa)
    (g : LinearMap.GeneralLinearGroup ℝ (SymbolF → ℝ))
    (hg : g ∈ (phi43RegularityStructureF κ).group) :
    ∃ p : G, ∀ τ : Symbol, g.val (Pi.single (.old τ) 1) =
      phi43OldEmbF (phi43CoordinateEquiv (structureBasisAction p τ)) := by
  obtain ⟨g₀, ⟨p, rfl⟩, h⟩ := phi43ExtensionGroupF_old_action κ g hg
  refine ⟨p, fun τ => ?_⟩
  rw [← phi43OldEmbF_single, h, phi43StructureGroupElement_apply_single, structureGroupMap_basis]

theorem phi43CoordinateEquiv_single (a : Symbol) (r : ℝ) :
    phi43CoordinateEquiv (Finsupp.single a r) = r • Pi.single a 1 := by
  rw [← Finsupp.smul_single_one, map_smul, ← phi43CoordinateEquiv_basis]
  rfl

theorem phi43ProductLinearF_oldEmb (u w : T) :
    phi43ProductLinearF (phi43OldEmbF (phi43CoordinateEquiv u))
        (phi43OldEmbF (phi43CoordinateEquiv w)) =
      phi43OldEmbF (phi43CoordinateEquiv (u * w)) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u₁ u₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, multiply_add_left, h₁, h₂]
  | single a r =>
    induction w using Finsupp.induction_linear with
    | zero => simp
    | add w₁ w₂ h₁ h₂ => simp only [map_add, multiply_add_right, h₁, h₂]
    | single b s =>
      rw [phi43CoordinateEquiv_single, phi43CoordinateEquiv_single, multiply_single, map_smul,
        map_smul, map_smul, map_smul, LinearMap.smul_apply, map_smul, map_smul,
        phi43OldEmbF_single, phi43OldEmbF_single, phi43ProductLinearF_old_basis, multiply_basis,
        smul_smul, mul_comm]

end RegularityStructures.Phi43

end
