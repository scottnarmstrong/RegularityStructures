/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.Abstract
public import Phi43.Structure.AbstractIntegration
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Abstract.Singular.Phi4FixedPointBlock
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# Block-projection obstructions on the 20-symbol Φ⁴₃ structure

On `phi43RegularityStructure κ`, every admissible block `A` of a block-projected fixed point (one
whose model satisfies the block invariance `hA : Γ_{xy} ∘ P_A = P_A ∘ Γ_{xy}`) must exclude `Ψ` and
`Ψ²`:

* (i) `Ψ² ∈ A`, `I(Ψ³)Ψ² ∉ A`: `hA` forces `(Γ_{xy} I(Ψ³)Ψ²)_{Ψ²} = 0` (`hA_forces_zero`), while
  the group coordinate is `cPsiCube` (`group_iPsiCubePsiSq_psiSq`);
* (ii) `I(Ψ³)Ψ² ∈ A`: `IsAbstractIntegration (blockSpan A) phi43AbstractIntegration 2` fails
  (`not_isAbstractIntegration`);
* (iii) `A = {Ψ, Ψ², Ψ³}`: `hA` forces `(Γ_{xy} Xᵢ)_1 = 0`, incompatible with polynomial
  compatibility for every model (`hA_forces_zero_shift`);
* (iv) `ΨX₀ ∈ A` (spatial index `0`): `IsAbstractIntegration` fails
  (`not_isAbstractIntegration_psiX`).

This is why the fixed point is stated on the enlarged structure, with `A` the `Ξ`-free symbols.
-/

namespace Regression.BlockProjection

open RegularityStructures RegularityStructures.Phi43

/-- The block `A = {Ψ, Ψ², Ψ³}`. -/
def cubicBlock : Finset Symbol := {.psi, .psiSq, .psiCube}

/-- (i) The block invariance `hA` with `A ∋ Ψ²`, `A ∌ I(Ψ³)Ψ²` forces the `Ψ²`-coordinate of
`Γ_{xy} I(Ψ³)Ψ²` to vanish for every pair of points. -/
theorem hA_forces_zero (κ : Kappa)
    (M : Model (phi43RegularityStructure κ) parabolicSemigroup)
    (hA : ∀ x y τ, M.gammaMap x y (blockProj cubicBlock τ) =
      blockProj cubicBlock (M.gammaMap x y τ)) (x y : ParabolicSpace) :
    M.gammaMap x y (Pi.single .iPsiCubePsiSq 1) .psiSq = 0 := by
  have h := congrFun (hA x y (Pi.single .iPsiCubePsiSq 1)) .psiSq
  have h0 : blockProj cubicBlock (Pi.single Symbol.iPsiCubePsiSq (1 : ℝ)) = 0 := by
    funext i
    by_cases hi : i = .iPsiCubePsiSq
    · subst hi; simp [blockProj_apply, cubicBlock]
    · simp [blockProj_apply, hi]
  rw [h0, map_zero] at h
  have hmem : Symbol.psiSq ∈ cubicBlock := by simp [cubicBlock]
  rw [blockProj_apply_of_mem hmem] at h
  simpa using h.symm

/-- (i) In the group, `Γ_g I(Ψ³)Ψ²` has `Ψ²`-coordinate `g.cPsiCube`. -/
theorem group_iPsiCubePsiSq_psiSq (g : G) :
    (phi43StructureGroupElement g : (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ))
      (Pi.single .iPsiCubePsiSq 1) .psiSq = g.cPsiCube := by
  rw [phi43StructureGroupElement_apply_single, structureGroupMap_basis]
  simp [structureBasisAction, primitiveAction, phi43CoordinateEquiv, basisProduct,
    productSymbol, basis]

/-- (ii) If `A` contains `I(Ψ³)Ψ²`, the abstract integration `phi43AbstractIntegration` fails the
commutation field of `IsAbstractIntegration` on `blockSpan A`, for any polynomial sector whose span
does not contain `I(Ψ²)`. In particular this excludes the blocks containing both `Ψ²` and
`I(Ψ³)Ψ²`. -/
theorem not_isAbstractIntegration (κ : Kappa) {N' : ℕ}
    (Ppoly : PolynomialSector (phi43RegularityStructure κ) N') (A : Finset Symbol)
    (h2 : Symbol.iPsiCubePsiSq ∈ A)
    (hpoly : Symbol.iPsiSq ∉ Set.range Ppoly.emb) :
    ¬ IsAbstractIntegration Ppoly (blockSpan A) phi43AbstractIntegration 2 := by
  intro hI
  let g : G := ⟨0, 0, 0, 0, 1⟩
  have ha : (Pi.single Symbol.iPsiCubePsiSq (1 : ℝ) : Symbol → ℝ) ∈ blockSpan A :=
    Submodule.subset_span ⟨_, h2, rfl⟩
  have hc := hI.comm (phi43StructureGroupElement g) (phi43RegularityStructure_group_mem κ g) _ ha
  have hzero : phi43AbstractIntegration (Pi.single Symbol.iPsiCubePsiSq (1 : ℝ)) = 0 := by
    funext i
    simp [phi43AbstractIntegration_apply, phi43CoordinateEquiv, integration,
      integrationBasisAction]
  rw [hzero, map_zero, sub_zero] at hc
  have hval := hc .iPsiSq hpoly
  rw [phi43StructureGroupElement_apply_single, structureGroupMap_basis] at hval
  simp [structureBasisAction, primitiveAction, phi43CoordinateEquiv, g, basisProduct,
    productSymbol, basis, phi43AbstractIntegration_apply, integration,
    integrationBasisAction] at hval

/-- (iii) In the group, `(Γ_g (Ψ Xᵢ))_Ψ = (Γ_g Xᵢ)_1`: both are the spatial shift of `g`. -/
theorem group_psiX_psi_eq_x_one (g : G) (i : Fin 3) :
    (phi43StructureGroupElement g : (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ))
        (Pi.single (.psiX i) 1) .psi =
      (phi43StructureGroupElement g : (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ))
        (Pi.single (.x i) 1) .one := by
  rw [phi43StructureGroupElement_apply_single, phi43StructureGroupElement_apply_single,
    structureGroupMap_basis, structureGroupMap_basis]
  simp [structureBasisAction, primitiveAction, phi43CoordinateEquiv, basisProduct,
    productSymbol, basis]

/-- (iii) With the block `A = {Ψ, Ψ², Ψ³}`, the block invariance `hA` forces `(Γ_{xy} Xᵢ)_1 = 0` for all
`x, y`. Polynomial compatibility forces this entry to be `xᵢ - yᵢ`, so `hA` and `IsRealisingP`
are jointly unsatisfiable for *every* model, degenerate ones included. -/
theorem hA_forces_zero_shift (κ : Kappa)
    (M : Model (phi43RegularityStructure κ) parabolicSemigroup)
    (hA : ∀ x y τ, M.gammaMap x y (blockProj cubicBlock τ) =
      blockProj cubicBlock (M.gammaMap x y τ)) (x y : ParabolicSpace) (i : Fin 3) :
    M.gammaMap x y (Pi.single (.x i) 1) .one = 0 := by
  obtain ⟨g, hg⟩ := (M.gamma x y).2
  have h := congrFun (hA x y (Pi.single (.psiX i) 1)) .psi
  have h0 : blockProj cubicBlock (Pi.single (Symbol.psiX i) (1 : ℝ)) = 0 := by
    funext j
    by_cases hj : j = .psiX i
    · subst hj; simp [blockProj_apply, cubicBlock]
    · simp [blockProj_apply, hj]
  rw [h0, map_zero, blockProj_apply_of_mem (by simp [cubicBlock])] at h
  have e1 : M.gammaMap x y (Pi.single (.psiX i) 1) .psi =
      (phi43StructureGroupElement g : (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ))
        (Pi.single (.psiX i) 1) .psi := by
    simp only [Model.gammaMap, ← hg]
  have e2 : M.gammaMap x y (Pi.single (.x i) 1) .one =
      (phi43StructureGroupElement g : (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ))
        (Pi.single (.x i) 1) .one := by
    simp only [Model.gammaMap, ← hg]
  rw [e2, ← group_psiX_psi_eq_x_one, ← e1]
  simpa using h.symm

/-- (iv) If `A` contains `Ψ X₀`, the abstract integration `phi43AbstractIntegration` fails `IsAbstractIntegration` on
`blockSpan A`: `I(Ψ X₀) = 0` but `Γ_g(Ψ X₀) = Ψ X₀ + shift·Ψ` and `I Ψ = I(Ψ)` is not polynomial. -/
theorem not_isAbstractIntegration_psiX (κ : Kappa) {N' : ℕ}
    (Ppoly : PolynomialSector (phi43RegularityStructure κ) N') (A : Finset Symbol)
    (h2 : Symbol.psiX 0 ∈ A) (hpoly : Symbol.iPsi ∉ Set.range Ppoly.emb) :
    ¬ IsAbstractIntegration Ppoly (blockSpan A) phi43AbstractIntegration 2 := by
  intro hI
  let g : G := ⟨fun _ => 1, 0, 0, 0, 0⟩
  have ha : (Pi.single (Symbol.psiX 0) (1 : ℝ) : Symbol → ℝ) ∈ blockSpan A :=
    Submodule.subset_span ⟨_, h2, rfl⟩
  have hc := hI.comm (phi43StructureGroupElement g) (phi43RegularityStructure_group_mem κ g) _ ha
  have hzero : phi43AbstractIntegration (Pi.single (Symbol.psiX 0) (1 : ℝ)) = 0 := by
    funext i
    simp [phi43AbstractIntegration_apply, phi43CoordinateEquiv, integration,
      integrationBasisAction]
  rw [hzero, map_zero, sub_zero] at hc
  have hval := hc .iPsi hpoly
  rw [phi43StructureGroupElement_apply_single, structureGroupMap_basis] at hval
  simp [structureBasisAction, primitiveAction, phi43CoordinateEquiv, g, basisProduct,
    productSymbol, basis, phi43AbstractIntegration_apply, integration,
    integrationBasisAction] at hval

end Regression.BlockProjection
