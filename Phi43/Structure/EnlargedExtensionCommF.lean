/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.EnlargedOldActionF
public import Phi43.Structure.EnlargedGroupCharacterisationF
public import Phi43.Structure.QuadraticIntegration

/-!
# Commutation for the literal extension action

Hairer [Hai14, Theorem 5.14]. The new plants obey I Gamma by construction.
The old rows still require verification: their polynomial remainders
must be the genuine old Taylor remainders.
-/

public section

namespace RegularityStructures.Phi43

theorem phi43PlantExtensionLinearF_comm_planted (κ : Kappa)
    (g : LinearMap.GeneralLinearGroup ℝ (Symbol → ℝ))
    (hg : g ∈ (phi43RegularityStructure κ).group) (τ : Phi43PlantSource) :
    phi43IntegrationF (phi43PlantExtensionLinearF g.val (Pi.single (.planted τ) 1)) -
      phi43PlantExtensionLinearF g.val (phi43IntegrationF (Pi.single (.planted τ) 1)) = 0 := by
  rw [phi43IntegrationF_planted, map_zero, sub_zero, phi43PlantExtensionLinearF_single]
  change phi43IntegrationF (phi43IntegrationF
    (phi43OldEmbF (g.val (Pi.single τ.symbol 1)))) = 0
  apply phi43IntegrationF_sq_eq_zero
  change g.val (Pi.single τ.symbol 1) .noise = 0
  rw [phi43OldGroup_noise_single κ g hg]
  cases τ <;> simp [Phi43PlantSource.symbol]

private theorem source_fixed (κ : Kappa)
    (g : LinearMap.GeneralLinearGroup ℝ (Symbol → ℝ))
    (hg : g ∈ (phi43RegularityStructure κ).group) (τ : Symbol)
    (hτ : τ = .noise ∨ τ = .psi ∨ τ = .psiSq ∨ τ = .psiCube) :
    g.val (Pi.single τ 1) = Pi.single τ 1 := by
  obtain ⟨p, rfl⟩ := hg
  rw [phi43StructureGroupElement_apply_single, structureGroupMap_basis]
  rcases hτ with rfl | rfl | rfl | rfl
  all_goals simp [structureBasisAction, primitiveAction, multiply_basis,
    basisProduct, productSymbol, phi43CoordinateEquiv_basis]

private theorem source_integration (τ : Symbol)
    (hτ : τ = .noise ∨ τ = .psi ∨ τ = .psiSq ∨ τ = .psiCube) :
    phi43IntegrationF (phi43OldEmbF (Pi.single τ 1)) =
      phi43OldEmbF (phi43AbstractIntegration (Pi.single τ 1)) := by
  have he : phi43CoordinateEquiv.symm (Pi.single τ 1) = basis τ := by
    apply phi43CoordinateEquiv.injective
    simp [phi43CoordinateEquiv_basis]
  rw [phi43AbstractIntegration_apply, he, integration_basis, phi43OldEmbF_single,
    phi43IntegrationF_single]
  rcases hτ with rfl | rfl | rfl | rfl
  all_goals simp [phi43IntegrationSymbolF, integrationBasisAction,
    phi43CoordinateEquiv_basis, phi43OldEmbF_single]

private theorem comm_source (κ : Kappa)
    (g : LinearMap.GeneralLinearGroup ℝ (Symbol → ℝ))
    (hg : g ∈ (phi43RegularityStructure κ).group) (τ : Symbol)
    (hτ : τ = .noise ∨ τ = .psi ∨ τ = .psiSq ∨ τ = .psiCube) :
    phi43IntegrationF (phi43PlantExtensionLinearF g.val (Pi.single (.old τ) 1)) -
      phi43PlantExtensionLinearF g.val (phi43IntegrationF (Pi.single (.old τ) 1)) ∈
        phi43PolynomialSubspaceF κ := by
  have ha : (Pi.single τ 1 : Symbol → ℝ) ∈ phi43IntegrationSector := by
    rcases hτ with rfl | rfl | rfl | rfl
    all_goals intro σ _ _ _ _
    all_goals simp_all
  have hh := (phi43AbstractIntegration_isAbstractIntegration_quadratic κ).comm g hg _ ha
  rw [source_fixed κ g hg τ hτ] at hh
  rw [← phi43OldEmbF_single, phi43PlantExtensionLinearF_old, source_fixed κ g hg τ hτ,
    source_integration τ hτ, phi43PlantExtensionLinearF_old, ← map_sub]
  exact Submodule.mem_map_of_mem hh

private theorem comm_polynomial (κ : Kappa)
    (g : LinearMap.GeneralLinearGroup ℝ (Symbol → ℝ))
    (hg : g ∈ (phi43RegularityStructure κ).group) (τ : Symbol)
    (hτ : τ ∈ Set.range phi43QuadraticPolyEmb) :
    phi43IntegrationF (phi43PlantExtensionLinearF g.val (Pi.single (.old τ) 1)) -
      phi43PlantExtensionLinearF g.val (phi43IntegrationF (Pi.single (.old τ) 1)) ∈
        phi43PolynomialSubspaceF κ := by
  have ha : (Pi.single τ 1 : Symbol → ℝ) ∈ (phi43PolynomialSectorQuadratic κ).subspace := by
    intro σ hσ
    by_cases he : σ = τ
    · subst σ; exact False.elim (hσ hτ)
    · simp [he]
  have hb : phi43OldEmbF (Pi.single τ 1) ∈ phi43PolynomialSubspaceF κ :=
    Submodule.mem_map_of_mem ha
  have hc : phi43PlantExtensionLinearF g.val (phi43OldEmbF (Pi.single τ 1)) ∈
      phi43PolynomialSubspaceF κ := by
    rw [phi43PlantExtensionLinearF_old]
    exact Submodule.mem_map_of_mem ((phi43PolynomialSectorQuadratic κ).invariant g hg _ ha)
  have hIb := phi43IntegrationF_polynomial_zero κ _
    (by rw [phi43PolynomialSectorF_subspace]; exact hb)
  have hIc := phi43IntegrationF_polynomial_zero κ _
    (by rw [phi43PolynomialSectorF_subspace]; exact hc)
  rw [← phi43OldEmbF_single, hIc, hIb, map_zero, sub_self]
  exact Submodule.zero_mem _

private theorem comm_kernel (p : G) (τ : Symbol)
    (hτ : τ = .iPsi ∨ τ = .iPsiSq ∨ τ = .iPsiCube ∨ τ = .iPsiCubeSq) :
    phi43IntegrationF (phi43PlantExtensionLinearF (phi43StructureGroupElement p).val
        (Pi.single (.old τ) 1)) -
      phi43PlantExtensionLinearF (phi43StructureGroupElement p).val
        (phi43IntegrationF (Pi.single (.old τ) 1)) = 0 := by
  rcases hτ with rfl | rfl | rfl | rfl
  all_goals simp [phi43IntegrationF_single, phi43IntegrationSymbolF,
    phi43PlantExtensionLinearF_single, phi43PlantExtensionBasisF,
    phi43StructureGroupElement_apply_single, structureGroupMap_basis,
    structureBasisAction, primitiveAction, multiply_add_left, multiply_add_right,
    basisProduct, productSymbol, phi43CoordinateEquiv_basis, map_add, map_smul, map_sum,
    phi43OldEmbF_single]

theorem phi43PlantExtensionLinearF_comm_old (κ : Kappa)
    (g : LinearMap.GeneralLinearGroup ℝ (Symbol → ℝ))
    (hg : g ∈ (phi43RegularityStructure κ).group) (τ : Symbol) :
    phi43IntegrationF (phi43PlantExtensionLinearF g.val (Pi.single (.old τ) 1)) -
      phi43PlantExtensionLinearF g.val (phi43IntegrationF (Pi.single (.old τ) 1)) ∈
        phi43PolynomialSubspaceF κ := by
  by_cases hp : τ ∈ Set.range phi43QuadraticPolyEmb
  · exact comm_polynomial κ g hg τ hp
  by_cases hs : τ = .noise ∨ τ = .psi ∨ τ = .psiSq ∨ τ = .psiCube
  · exact comm_source κ g hg τ hs
  by_cases hk : τ = .iPsi ∨ τ = .iPsiSq ∨ τ = .iPsiCube ∨ τ = .iPsiCubeSq
  · obtain ⟨p, rfl⟩ := hg
    rw [comm_kernel p τ hk]
    exact Submodule.zero_mem _
  rw [phi43QuadraticPolyEmb_range] at hp
  cases τ <;> simp_all [phi43IntegrationF_single, phi43IntegrationSymbolF,
    phi43PlantExtensionLinearF_single, phi43PlantExtensionBasisF, Phi43PlantSource.symbol]

end RegularityStructures.Phi43

end
