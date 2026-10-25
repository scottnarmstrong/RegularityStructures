/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.AbstractPolynomial
public import Phi43.Structure.Renormalisation
import Mathlib.Tactic

/-!
# Abstract integration for the finite Φ⁴₃ structure

The abstract interface uses coefficient functions, while the concrete finite
integration map is defined on the free vector space.  This file transports the
concrete map across the finite coordinate equivalence and verifies the
algebraic clauses of Hairer [Hai14, Definition 5.7].
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The concrete integration map transported to the abstract coordinate space. -/
def phi43AbstractIntegration : (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ) :=
  phi43CoordinateEquiv.toLinearMap.comp
    (integration.comp phi43CoordinateEquiv.symm.toLinearMap)

theorem phi43AbstractIntegration_apply (a : Symbol → ℝ) :
    phi43AbstractIntegration a =
      phi43CoordinateEquiv (integration (phi43CoordinateEquiv.symm a)) := rfl

private theorem phi43CoordinateEquiv_symm_single (τ : Symbol) :
    phi43CoordinateEquiv.symm (Pi.single τ 1) = basis τ := by
  apply phi43CoordinateEquiv.injective
  simp [phi43CoordinateEquiv_basis]

private theorem phi43AbstractIntegration_single (τ : Symbol) :
    phi43AbstractIntegration (Pi.single τ 1) =
      match τ with
      | .noise => Pi.single .psi 1
      | .psi => Pi.single .iPsi 1
      | .psiSq => Pi.single .iPsiSq 1
      | .psiCube => Pi.single .iPsiCube 1
      | _ => 0 := by
  rw [phi43AbstractIntegration_apply, phi43CoordinateEquiv_symm_single]
  cases τ <;>
    simp [integration_basis, integrationBasisAction, phi43CoordinateEquiv_basis]

private theorem phi43AbstractIntegration_single_coord (τ i : Symbol) :
    phi43AbstractIntegration (Pi.single τ 1) i =
      match τ with
      | .noise => if i = .psi then 1 else 0
      | .psi => if i = .iPsi then 1 else 0
      | .psiSq => if i = .iPsiSq then 1 else 0
      | .psiCube => if i = .iPsiCube then 1 else 0
      | _ => 0 := by
  cases τ <;>
    simp [phi43AbstractIntegration_single, Pi.single_apply]

theorem phi43AbstractIntegration_apply_coord (a : Symbol → ℝ) (i : Symbol) :
    phi43AbstractIntegration a i =
      match i with
      | .psi => a .noise
      | .iPsi => a .psi
      | .iPsiSq => a .psiSq
      | .iPsiCube => a .psiCube
      | _ => 0 := by
  conv_lhs => rw [eq_sum_single a]
  simp only [map_sum, Finset.sum_apply, map_smul]
  cases i with
  | one =>
      apply Finset.sum_eq_zero
      intro τ _
      cases τ <;> simp [phi43AbstractIntegration_single_coord]
  | noise =>
      apply Finset.sum_eq_zero
      intro τ _
      cases τ <;> simp [phi43AbstractIntegration_single_coord]
  | x0 =>
      apply Finset.sum_eq_zero
      intro τ _
      cases τ <;> simp [phi43AbstractIntegration_single_coord]
  | x i =>
      apply Finset.sum_eq_zero
      intro τ _
      cases τ <;> simp [phi43AbstractIntegration_single_coord]
  | xMul p =>
      apply Finset.sum_eq_zero
      intro τ _
      cases τ <;> simp [phi43AbstractIntegration_single_coord]
  | psi =>
      rw [Finset.sum_eq_single_of_mem Symbol.noise (Finset.mem_univ Symbol.noise)]
      · simp [phi43AbstractIntegration_single_coord]
      · intro τ _ hτ
        cases τ <;> simp_all [phi43AbstractIntegration_single_coord]
  | psiSq =>
      apply Finset.sum_eq_zero
      intro τ _
      cases τ <;> simp [phi43AbstractIntegration_single_coord]
  | psiCube =>
      apply Finset.sum_eq_zero
      intro τ _
      cases τ <;> simp [phi43AbstractIntegration_single_coord]
  | psiX i =>
      apply Finset.sum_eq_zero
      intro τ _
      cases τ <;> simp [phi43AbstractIntegration_single_coord]
  | psiSqX i =>
      apply Finset.sum_eq_zero
      intro τ _
      cases τ <;> simp [phi43AbstractIntegration_single_coord]
  | iPsiSq =>
      rw [Finset.sum_eq_single_of_mem Symbol.psiSq (Finset.mem_univ Symbol.psiSq)]
      · simp [phi43AbstractIntegration_single_coord]
      · intro τ _ hτ
        cases τ <;> simp_all [phi43AbstractIntegration_single_coord]
  | iPsiCube =>
      rw [Finset.sum_eq_single_of_mem Symbol.psiCube (Finset.mem_univ Symbol.psiCube)]
      · simp [phi43AbstractIntegration_single_coord]
      · intro τ _ hτ
        cases τ <;> simp_all [phi43AbstractIntegration_single_coord]
  | iPsiPsi =>
      apply Finset.sum_eq_zero
      intro τ _
      cases τ <;> simp [phi43AbstractIntegration_single_coord]
  | iPsiPsiSq =>
      apply Finset.sum_eq_zero
      intro τ _
      cases τ <;> simp [phi43AbstractIntegration_single_coord]
  | iPsiSqPsi =>
      apply Finset.sum_eq_zero
      intro τ _
      cases τ <;> simp [phi43AbstractIntegration_single_coord]
  | iPsiSqPsiSq =>
      apply Finset.sum_eq_zero
      intro τ _
      cases τ <;> simp [phi43AbstractIntegration_single_coord]
  | iPsi =>
      rw [Finset.sum_eq_single_of_mem Symbol.psi (Finset.mem_univ Symbol.psi)]
      · simp [phi43AbstractIntegration_single_coord]
      · intro τ _ hτ
        cases τ <;> simp_all [phi43AbstractIntegration_single_coord]
  | iPsiCubePsi =>
      apply Finset.sum_eq_zero
      intro τ _
      cases τ <;> simp [phi43AbstractIntegration_single_coord]
  | iPsiCubePsiSq =>
      apply Finset.sum_eq_zero
      intro τ _
      cases τ <;> simp [phi43AbstractIntegration_single_coord]
  | iPsiCubeSq =>
      apply Finset.sum_eq_zero
      intro τ _
      cases τ <;> simp [phi43AbstractIntegration_single_coord]

/-- The sector on which the finite integration map is supported. -/
def phi43IntegrationSector : Submodule ℝ (Symbol → ℝ) where
  carrier := {a | ∀ τ, τ ≠ .noise → τ ≠ .psi → τ ≠ .psiSq → τ ≠ .psiCube → a τ = 0}
  add_mem' := by
    intro a b ha hb τ hτn hτp hτs hτc
    simp [ha τ hτn hτp hτs hτc, hb τ hτn hτp hτs hτc]
  zero_mem' := by
    intro τ hτn hτp hτs hτc
    rfl
  smul_mem' := by
    intro r a ha τ hτn hτp hτs hτc
    simp [ha τ hτn hτp hτs hτc]

private theorem phi43IntegrationSector_eq (a : Symbol → ℝ)
    (ha : a ∈ phi43IntegrationSector) :
    a = a .noise • (Pi.single .noise 1 : Symbol → ℝ) + a .psi • (Pi.single .psi 1 : Symbol → ℝ) +
      a .psiSq • (Pi.single .psiSq 1 : Symbol → ℝ) +
      a .psiCube • (Pi.single .psiCube 1 : Symbol → ℝ) := by
  ext τ
  cases τ <;> simp [phi43IntegrationSector] at ha ⊢
  all_goals exact ha _ (by simp) (by simp) (by simp) (by simp)

private theorem phi43Group_fix_noise (g : G) :
    (phi43StructureGroupElement g : (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ))
        (Pi.single .noise 1) = Pi.single .noise 1 := by
  rw [phi43StructureGroupElement_apply_single]
  simp [phi43CoordinateEquiv_basis, structureGroupMap_basis, structureBasisAction,
    primitiveAction]

private theorem phi43Group_fix_psi (g : G) :
    (phi43StructureGroupElement g : (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ))
        (Pi.single .psi 1) = Pi.single .psi 1 := by
  rw [phi43StructureGroupElement_apply_single]
  simp [phi43CoordinateEquiv_basis, structureGroupMap_basis, structureBasisAction,
    primitiveAction]

private theorem phi43Group_fix_psiSq (g : G) :
    (phi43StructureGroupElement g : (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ))
        (Pi.single .psiSq 1) = Pi.single .psiSq 1 := by
  rw [phi43StructureGroupElement_apply_single]
  simp [phi43CoordinateEquiv_basis, structureGroupMap_basis, structureBasisAction,
    primitiveAction, multiply_basis, basisProduct, productSymbol]

private theorem phi43Group_fix_psiCube (g : G) :
    (phi43StructureGroupElement g : (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ))
        (Pi.single .psiCube 1) = Pi.single .psiCube 1 := by
  rw [phi43StructureGroupElement_apply_single]
  simp [phi43CoordinateEquiv_basis, structureGroupMap_basis, structureBasisAction,
    primitiveAction, multiply_basis, basisProduct, productSymbol]

private theorem phi43AbstractIntegration_map_homogeneous (κ : Kappa) {α : ℝ}
    {a : Symbol → ℝ} (_ha : a ∈ phi43IntegrationSector)
    (haα : a ∈ RegularityStructures.homogeneousSubspace
      (phi43RegularityStructure κ).deg α) :
    phi43AbstractIntegration a ∈
      RegularityStructures.homogeneousSubspace (phi43RegularityStructure κ).deg (α + 2) := by
  change ∀ i, homogeneity κ i ≠ α + 2 → phi43AbstractIntegration a i = 0
  change ∀ i, homogeneity κ i ≠ α → a i = 0 at haα
  intro i hi
  rw [phi43AbstractIntegration_apply_coord]
  cases i with
  | one => rfl
  | noise => rfl
  | x0 => rfl
  | x i => rfl
  | xMul p => rfl
  | psi =>
      by_cases hα : homogeneity κ .noise = α
      · have hrel : homogeneity κ .psi = homogeneity κ .noise + 2 := by
          simp [homogeneity]
          ring
        exfalso
        apply hi
        linarith
      · simp [haα .noise hα]
  | psiSq => rfl
  | psiCube => rfl
  | psiX i => rfl
  | psiSqX i => rfl
  | iPsiSq =>
      by_cases hα : homogeneity κ .psiSq = α
      · have hrel : homogeneity κ .iPsiSq = homogeneity κ .psiSq + 2 := by
          simp [homogeneity]
          ring
        exfalso
        apply hi
        linarith
      · simp [haα .psiSq hα]
  | iPsiCube =>
      by_cases hα : homogeneity κ .psiCube = α
      · have hrel : homogeneity κ .iPsiCube = homogeneity κ .psiCube + 2 := by
          simp [homogeneity]
          ring
        exfalso
        apply hi
        linarith
      · simp [haα .psiCube hα]
  | iPsi =>
      by_cases hα : homogeneity κ .psi = α
      · have hrel : homogeneity κ .iPsi = homogeneity κ .psi + 2 := by
          simp [homogeneity]
          ring
        exfalso
        apply hi
        linarith
      · simp [haα .psi hα]
  | iPsiPsi => rfl
  | iPsiPsiSq => rfl
  | iPsiSqPsi => rfl
  | iPsiSqPsiSq => rfl
  | iPsiCubePsi => rfl
  | iPsiCubePsiSq => rfl
  | iPsiCubeSq => rfl

private theorem phi43IntegrationSector_map (g : G) (a : Symbol → ℝ)
    (ha : a ∈ phi43IntegrationSector) :
    (phi43StructureGroupElement g : (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ)) a = a := by
  rw [phi43IntegrationSector_eq a ha]
  simp only [map_add, map_smul, phi43Group_fix_noise, phi43Group_fix_psi,
    phi43Group_fix_psiSq, phi43Group_fix_psiCube]

theorem phi43IntegrationSector_isSector (κ : Kappa) :
    (phi43RegularityStructure κ).IsSector phi43IntegrationSector where
  graded α a ha := by
    intro τ hτn hτp hτs hτc
    rw [RegularityStructures.homogeneousProj_apply]
    split_ifs with hα
    · exact ha τ hτn hτp hτs hτc
    · rfl
  invariant g hg a ha := by
    rcases hg with ⟨g, rfl⟩
    rw [phi43IntegrationSector_map g a ha]
    exact ha

private theorem phi43Integration_map_poly_zero (κ : Kappa) {a : Symbol → ℝ}
    (_ha : a ∈ phi43IntegrationSector)
    (haP : a ∈ (phi43PolynomialSector κ).subspace) :
    a .noise = 0 ∧ a .psi = 0 ∧ a .psiSq = 0 ∧ a .psiCube = 0 := by
  have hn : .noise ∉ Set.range phi43PolyEmb := by
    intro hn
    obtain ⟨k, hk⟩ := hn
    rcases polyIndex_two_cases k with h | h | h | h <;>
      simp [phi43PolyEmb, h] at hk
  have hs : .psiSq ∉ Set.range phi43PolyEmb := by
    intro hs
    obtain ⟨k, hk⟩ := hs
    rcases polyIndex_two_cases k with h | h | h | h <;>
      simp [phi43PolyEmb, h] at hk
  have hp : .psi ∉ Set.range phi43PolyEmb := by
    intro hp
    obtain ⟨k, hk⟩ := hp
    rcases polyIndex_two_cases k with h | h | h | h <;>
      simp [phi43PolyEmb, h] at hk
  have hc : .psiCube ∉ Set.range phi43PolyEmb := by
    intro hc
    obtain ⟨k, hk⟩ := hc
    rcases polyIndex_two_cases k with h | h | h | h <;>
      simp [phi43PolyEmb, h] at hk
  exact ⟨haP .noise hn, haP .psi hp, haP .psiSq hs, haP .psiCube hc⟩

private theorem phi43_poly_single_x_mem (κ : Kappa) (i : Fin 3) :
    Pi.single (.x i) 1 ∈ (phi43PolynomialSector κ).subspace := by
  fin_cases i
  · let k : PolyIndex 2 :=
      ⟨Finsupp.single (1 : Fin 4) 1, by simp [weight_parabolicWeight]⟩
    have hk : phi43PolyEmb k = .x 0 := by simp [k, phi43PolyEmb]
    intro j hj
    simp only [Pi.single_apply]
    split_ifs with h
    · exact False.elim (hj ⟨k, hk.trans h.symm⟩)
    · rfl
  · let k : PolyIndex 2 :=
      ⟨Finsupp.single (2 : Fin 4) 1, by simp [weight_parabolicWeight]⟩
    have hk : phi43PolyEmb k = .x 1 := by simp [k, phi43PolyEmb]
    intro j hj
    simp only [Pi.single_apply]
    split_ifs with h
    · exact False.elim (hj ⟨k, hk.trans h.symm⟩)
    · rfl
  · let k : PolyIndex 2 :=
      ⟨Finsupp.single (3 : Fin 4) 1, by simp [weight_parabolicWeight]⟩
    have hk : phi43PolyEmb k = .x 2 := by simp [k, phi43PolyEmb]
    intro j hj
    simp only [Pi.single_apply]
    split_ifs with h
    · exact False.elim (hj ⟨k, hk.trans h.symm⟩)
    · rfl

theorem phi43AbstractIntegration_isAbstractIntegration (κ : Kappa) :
    IsAbstractIntegration (phi43PolynomialSector κ) phi43IntegrationSector
      phi43AbstractIntegration 2 where
  pos := by norm_num
  map_homogeneous α a ha haα := phi43AbstractIntegration_map_homogeneous κ ha haα
  map_poly a ha haP := by
    rcases phi43Integration_map_poly_zero κ ha haP with ⟨hn, hp, hs, hc⟩
    funext i
    rw [phi43AbstractIntegration_apply_coord]
    cases i <;> simp [hn, hp, hs, hc]
  comm g hg a ha := by
    rcases hg with ⟨g, rfl⟩
    rw [phi43IntegrationSector_map g a ha]
    rw [phi43IntegrationSector_eq a ha]
    simp only [map_add, map_smul]
    have hpsi :
        (phi43StructureGroupElement g : (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ))
            (Pi.single .psi 1) = Pi.single .psi 1 := by
      rw [phi43StructureGroupElement_apply_single]
      simp [phi43CoordinateEquiv_basis, structureGroupMap_basis, structureBasisAction,
        primitiveAction]
    have hip :
        (phi43StructureGroupElement g : (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ))
            (Pi.single .iPsi 1) =
          (Pi.single .iPsi 1 : Symbol → ℝ) + g.cPsi • (Pi.single .one 1 : Symbol → ℝ) +
            ∑ i, g.cPsiGrad i • (Pi.single (.x i) 1 : Symbol → ℝ) := by
      rw [phi43StructureGroupElement_apply_single]
      simp [phi43CoordinateEquiv_basis, structureGroupMap_basis, structureBasisAction,
        primitiveAction]
    have hsq :
        (phi43StructureGroupElement g : (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ))
            (Pi.single .iPsiSq 1) =
          Pi.single .iPsiSq 1 + g.cPsiSq • Pi.single .one 1 := by
      rw [phi43StructureGroupElement_apply_single]
      simp [phi43CoordinateEquiv_basis, structureGroupMap_basis, structureBasisAction,
        primitiveAction]
    have hcube :
        (phi43StructureGroupElement g : (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ))
            (Pi.single .iPsiCube 1) =
          Pi.single .iPsiCube 1 + g.cPsiCube • Pi.single .one 1 := by
      rw [phi43StructureGroupElement_apply_single]
      simp [phi43CoordinateEquiv_basis, structureGroupMap_basis, structureBasisAction,
        primitiveAction]
    simp_rw [phi43AbstractIntegration_single]
    rw [hpsi, hip, hsq, hcube]
    have hcomm :
        a .noise • (Pi.single .psi 1 : Symbol → ℝ) + a .psi • (Pi.single .iPsi 1 : Symbol → ℝ) +
            a .psiSq • (Pi.single .iPsiSq 1 : Symbol → ℝ) +
            a .psiCube • (Pi.single .iPsiCube 1 : Symbol → ℝ) -
          (a .noise • (Pi.single .psi 1 : Symbol → ℝ) +
            a .psi • (Pi.single .iPsi 1 + g.cPsi • (Pi.single .one 1 : Symbol → ℝ) +
              ∑ i, g.cPsiGrad i • (Pi.single (.x i) 1 : Symbol → ℝ)) +
            a .psiSq • (Pi.single .iPsiSq 1 + g.cPsiSq • (Pi.single .one 1 : Symbol → ℝ)) +
            a .psiCube • (Pi.single .iPsiCube 1 +
              g.cPsiCube • (Pi.single .one 1 : Symbol → ℝ))) =
        -(a .psi * g.cPsi + a .psiSq * g.cPsiSq +
          a .psiCube * g.cPsiCube) •
            (Pi.single .one 1 : Symbol → ℝ) -
          a .psi • ∑ i, g.cPsiGrad i • (Pi.single (.x i) 1 : Symbol → ℝ) := by
      module
    rw [hcomm]
    apply Submodule.sub_mem
    · apply Submodule.smul_mem _ _
      let k : PolyIndex 2 := ⟨0, by simp [weight_parabolicWeight]⟩
      have hk : phi43PolyEmb k = .one := by
        simp [k, phi43PolyEmb]
      intro i hi
      have hone : i ≠ .one := by
        intro h
        apply hi
        exact ⟨k, hk.trans h.symm⟩
      simp [hone]
    · apply Submodule.smul_mem _ _
      apply Submodule.sum_mem _
      intro i hi
      apply Submodule.smul_mem _ _
      exact phi43_poly_single_x_mem κ i

end RegularityStructures.Phi43

end
