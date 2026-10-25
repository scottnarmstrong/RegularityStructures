/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Pinned.PiPinned
public import Phi43.Pinned.GroupParameters
import Mathlib.Tactic
public import RegularityStructures.Abstract.Model

/-!
# `Γ` is pinned (away from the time coordinate)

Two models `Z`, `Z'` with `Statements.IsRenormalisedCanonicalModel N κ noise C` have the same
`Γ_{xy} e_τ` for every symbol `τ ≠ X₀` (`gammaMap_single_eq_of_isRenormalisedCanonicalModel`).

The exception `τ = X₀` is genuine: `Γ_{xy} X₀ = X₀ + shift₀(x,y) · 1`, the time shift occurs in
no other `Γ_{xy} e_τ`, `X₀` has degree `2 > γ`, and nothing in the predicate constrains `Π X₀`
(see the module docstring of `Phi43.Pinned`).
-/

public section

namespace RegularityStructures.Phi43

open RegularityStructures

variable {N : ℕ} {κ : Kappa} {noise : CanonicalNoise} {C : RenormalisationConstants}
  {Z Z' : Model (phi43RegularityStructure κ) parabolicSemigroup}

private theorem not_mem_range_emb_ne {σ : Symbol} (hσ : σ ∉ Set.range phi43PolyEmb) :
    σ ≠ .one ∧ ∀ i : Fin 3, σ ≠ .x i :=
  ⟨fun h => hσ (h ▸ one_mem_range_phi43PolyEmb),
    fun i h => hσ (h ▸ x_mem_range_phi43PolyEmb i)⟩

/-- `Γ e_σ - e_σ ∈ T̄` for `σ ∈ {I(Ψ), I(Ψ²), I(Ψ³)}`. -/
private theorem structureGroupElement_sub_single_mem (κ : Kappa) (g : G) {σ : Symbol}
    (hσ : σ = .iPsi ∨ σ = .iPsiSq ∨ σ = .iPsiCube) :
    (phi43StructureGroupElement g : (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ)) (Pi.single σ 1) -
      Pi.single σ 1 ∈ (phi43PolynomialSector κ).subspace := by
  intro τ hτ
  obtain ⟨h1, h2⟩ := not_mem_range_emb_ne hτ
  rw [phi43StructureGroupElement_apply_single]
  rcases hσ with rfl | rfl | rfl
  · simp [phi43CoordinateEquiv, structureBasisAction, primitiveAction, basis,
      Pi.single_apply, h1, h2]
  · simp [phi43CoordinateEquiv, structureBasisAction, primitiveAction, basis,
      Pi.single_apply, h1]
  · simp [phi43CoordinateEquiv, structureBasisAction, primitiveAction, basis,
      Pi.single_apply, h1]

private theorem exists_group_param (κ : Kappa) (M : Model (phi43RegularityStructure κ) parabolicSemigroup)
    (x y : ParabolicSpace) :
    ∃ g : G, M.gammaMap x y =
      (phi43StructureGroupElement g : (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ)) := by
  obtain ⟨g, hg⟩ := (M.gamma x y).2
  exact ⟨g, by rw [Model.gammaMap, ← hg]⟩

private theorem basisAction_eq_of_apply_eq {g g' : G} {τ : Symbol}
    (h : (phi43StructureGroupElement g : (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ)) (Pi.single τ 1) =
      (phi43StructureGroupElement g' : (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ)) (Pi.single τ 1)) :
    structureBasisAction g τ = structureBasisAction g' τ := by
  rw [phi43StructureGroupElement_apply_single, phi43StructureGroupElement_apply_single] at h
  rw [structureGroupMap_basis, structureGroupMap_basis] at h
  exact phi43CoordinateEquiv.injective h

/-- On the polynomial symbols `X_i`, `Γ` is model independent. -/
private theorem gammaMap_x_eq (hZ : Statements.IsRenormalisedCanonicalModel N κ noise C Z)
    (hZ' : Statements.IsRenormalisedCanonicalModel N κ noise C Z') (i : Fin 3) (x y : ParabolicSpace) :
    Z.gammaMap x y (Pi.single (.x i) 1) = Z'.gammaMap x y (Pi.single (.x i) 1) := by
  obtain ⟨k, hk⟩ := x_mem_range_phi43PolyEmb i
  have hk' : (phi43PolynomialSector κ).emb k = .x i := hk
  rw [← hk', Model.gammaMap_single_emb hZ.1.poly, Model.gammaMap_single_emb hZ'.1.poly]

/-- On `I(Ψ)`, `I(Ψ²)`, `I(Ψ³)`, `Γ` is determined by the pinned `Π`. -/
private theorem gammaMap_integrated_eq (hZ : Statements.IsRenormalisedCanonicalModel N κ noise C Z)
    (hZ' : Statements.IsRenormalisedCanonicalModel N κ noise C Z') {σ : Symbol}
    (hσ : σ = .iPsi ∨ σ = .iPsiSq ∨ σ = .iPsiCube) (x y : ParabolicSpace) :
    Z.gammaMap x y (Pi.single σ 1) = Z'.gammaMap x y (Pi.single σ 1) := by
  have hpin : IsPinnedSymbol σ := by
    rcases hσ with rfl | rfl | rfl <;> simp [IsPinnedSymbol]
  obtain ⟨g, hg⟩ := exists_group_param κ Z x y
  obtain ⟨g', hg'⟩ := exists_group_param κ Z' x y
  have hv := structureGroupElement_sub_single_mem κ g hσ
  have hv' := structureGroupElement_sub_single_mem κ g' hσ
  have := Model.eq_of_regPi_eq_of_mem hZ.1.poly hZ'.1.poly x hv hv' (fun t ht z => by
    have a := Model.regPi_gammaMap Z x y (Pi.single σ 1) t z
    have a' := Model.regPi_gammaMap Z' x y (Pi.single σ 1) t z
    rw [hg] at a
    rw [hg'] at a'
    rw [Model.regPi_sub, Model.regPi_sub, a, a', regPi_eq_of_isRenormalisedCanonicalModel hZ hZ' hpin x ht z,
      regPi_eq_of_isRenormalisedCanonicalModel hZ hZ' hpin y ht z])
  rw [hg, hg']
  exact sub_left_injective this

/-- **`Γ` is pinned away from `X₀`.** Two models satisfying
`IsRenormalisedCanonicalModel N κ noise C` have the same `Γ_{xy} e_τ` for every symbol `τ ≠ X₀`.
(For `τ = X₀` the statement is false, see the module docstring.) -/
theorem gammaMap_single_eq_of_isRenormalisedCanonicalModel
    (hZ : Statements.IsRenormalisedCanonicalModel N κ noise C Z)
    (hZ' : Statements.IsRenormalisedCanonicalModel N κ noise C Z') {τ : Symbol} (hτ : τ ≠ .x0)
    (x y : ParabolicSpace) :
    Z.gammaMap x y (Pi.single τ 1) = Z'.gammaMap x y (Pi.single τ 1) := by
  obtain ⟨g, hg⟩ := exists_group_param κ Z x y
  obtain ⟨g', hg'⟩ := exists_group_param κ Z' x y
  have hx : ∀ i : Fin 3, structureBasisAction g (.x i) = structureBasisAction g' (.x i) :=
    fun i => basisAction_eq_of_apply_eq (by rw [← hg, ← hg']; exact gammaMap_x_eq hZ hZ' i x y)
  have h1 := fun σ (hσ : σ = .iPsi ∨ σ = .iPsiSq ∨ σ = .iPsiCube) =>
    basisAction_eq_of_apply_eq (g := g) (g' := g') (τ := σ)
      (by rw [← hg, ← hg']; exact gammaMap_integrated_eq hZ hZ' hσ x y)
  have hp := sameParametersExceptTime_of_basisAction hx (h1 _ (Or.inl rfl))
    (h1 _ (Or.inr (Or.inl rfl))) (h1 _ (Or.inr (Or.inr rfl)))
  rw [hg, hg', phi43StructureGroupElement_apply_single, phi43StructureGroupElement_apply_single,
    structureGroupMap_basis, structureGroupMap_basis, structureBasisAction_congr hp hτ]

end RegularityStructures.Phi43

end
