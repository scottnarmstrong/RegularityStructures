/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.EnlargedExtensionLinearF
public import Phi43.Structure.EnlargedIntegrationSquareF

/-!
# Noise-coordinate identities for the old and extended actions

Hairer [Hai14, Section 8.1, Theorem 5.14]. Raw noise is fixed, and no
other basis symbol acquires a raw-noise component. These identities are
derived from the actual old action, not supplied by a model.
-/

public section

namespace RegularityStructures.Phi43

theorem phi43OldGroup_noise_single (κ : Kappa)
    (g : LinearMap.GeneralLinearGroup ℝ (Symbol → ℝ))
    (hg : g ∈ (phi43RegularityStructure κ).group) (τ : Symbol) :
    g.val (Pi.single τ 1) .noise = (Pi.single τ 1 : Symbol → ℝ) .noise := by
  obtain ⟨p, rfl⟩ := hg
  rw [phi43StructureGroupElement_apply_single, structureGroupMap_basis]
  cases τ <;>
    simp [structureBasisAction, primitiveAction, integratedPsiProductAction,
      multiply_add_left, multiply_add_right,
      basisProduct, productSymbol, phi43CoordinateEquiv, basis]
  rename_i q
  induction q using Sym2.inductionOn with
  | _ i j =>
    simp [xMulAction_mk, primitiveAction, multiply_add_left, multiply_add_right,
      basisProduct, productSymbol, basis]

theorem phi43OldGroup_noise_coord (κ : Kappa)
    (g : LinearMap.GeneralLinearGroup ℝ (Symbol → ℝ))
    (hg : g ∈ (phi43RegularityStructure κ).group) (a : Symbol → ℝ) :
    g.val a .noise = a .noise := by
  conv_lhs => rw [eq_sum_single a]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    phi43OldGroup_noise_single κ g hg]
  simpa only [Finset.sum_apply, Pi.smul_apply] using congrFun (eq_sum_single a).symm .noise

theorem phi43PlantExtensionLinearF_noise_single (κ : Kappa)
    (g : LinearMap.GeneralLinearGroup ℝ (Symbol → ℝ))
    (hg : g ∈ (phi43RegularityStructure κ).group) (τ : SymbolF) :
    phi43PlantExtensionLinearF g.val (Pi.single τ 1) (.old .noise) =
      (Pi.single τ 1 : SymbolF → ℝ) (.old .noise) := by
  rw [phi43PlantExtensionLinearF_single]
  cases τ with
  | old τ =>
    simpa [phi43PlantExtensionBasisF, phi43OldEmbF, Pi.single_apply] using
      phi43OldGroup_noise_single κ g hg τ
  | planted τ => rfl

end RegularityStructures.Phi43

end
