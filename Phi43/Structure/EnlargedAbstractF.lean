/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.EnlargedGroupAlgebraF
public import RegularityStructures.Abstract.Singular.Slab.BlockProj

/-!
# The enlarged regularity structure and its Xi-free block

Hairer [Hai14, Definition 2.1, Definition 5.7, Theorem 5.14]. The finite
planted completion has its genuine extension subgroup. The Xi-free block
commutes with every group action, without any hypothesis on a model.
In the original finite structure, commutation of the block projection with the
structure group is incompatible with polynomial admissibility; the enlargement
removes this obstruction.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- The finite planted regularity structure used by the fixed-point extension. -/
def phi43RegularityStructureF (κ : Kappa) : RegularityStructure SymbolF where
  deg := phi43DegreeF κ
  group := phi43ExtensionGroupF κ
  isGradedUnipotent := fun _ hg => hg.1

end RegularityStructures.Phi43

end

public section

namespace RegularityStructures.Phi43

theorem phi43RegularityStructureF_old_deg (κ : Kappa) (τ : Symbol) :
    (phi43RegularityStructureF κ).deg (.old τ) = homogeneity κ τ := rfl

theorem phi43ExtensionGroupF_old_action (κ : Kappa)
    (g : LinearMap.GeneralLinearGroup ℝ (SymbolF → ℝ))
    (hg : g ∈ (phi43RegularityStructureF κ).group) :
    ∃ g₀ ∈ (phi43RegularityStructure κ).group,
      ∀ a, g.val (phi43OldEmbF a) = phi43OldEmbF (g₀.val a) := by
  obtain ⟨_, g₀, hg₀, h, _⟩ := hg
  exact ⟨g₀, hg₀, h⟩

theorem phi43ExtensionGroupF_noise_coord (κ : Kappa)
    (g : LinearMap.GeneralLinearGroup ℝ (SymbolF → ℝ))
    (hg : g ∈ (phi43RegularityStructureF κ).group) (a : SymbolF → ℝ) :
    g.val a (.old .noise) = a (.old .noise) := hg.2.choose_spec.2.2.2 a

private theorem old_noise_fixed (κ : Kappa)
    (g : LinearMap.GeneralLinearGroup ℝ (Symbol → ℝ))
    (hg : g ∈ (phi43RegularityStructure κ).group) :
    g.val (Pi.single .noise 1) = Pi.single .noise 1 := by
  obtain ⟨p, rfl⟩ := hg
  rw [phi43StructureGroupElement_apply_single, structureGroupMap_basis]
  simp [structureBasisAction, primitiveAction, phi43CoordinateEquiv, basis]

theorem phi43ExtensionGroupF_noise_fixed (κ : Kappa)
    (g : LinearMap.GeneralLinearGroup ℝ (SymbolF → ℝ))
    (hg : g ∈ (phi43RegularityStructureF κ).group) :
    g.val (Pi.single (.old .noise) 1) = Pi.single (.old .noise) 1 := by
  obtain ⟨g₀, hg₀, h⟩ := phi43ExtensionGroupF_old_action κ g hg
  rw [← phi43OldEmbF_single, h, old_noise_fixed κ g₀ hg₀, phi43OldEmbF_single]

end RegularityStructures.Phi43

end
