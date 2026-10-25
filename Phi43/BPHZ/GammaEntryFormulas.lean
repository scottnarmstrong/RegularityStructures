/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

import Mathlib.Tactic
public import Phi43.Structure.ModelSpace
public import Mathlib.Tactic.Module

/-!
# Explicit entries of the structure-group map

For `g : G` with the five parameters `shift`, `cPsi`, `cPsiGrad`, `cPsiSq`, `cPsiCube`, we give
`structureGroupMap g (basis τ)` coordinatewise for each of the 20 symbols `τ`.  Writing
`1 = basis .one`, `Xᵢ = basis (.x i)` and `sᵢ = g.shift i.succ`:

* `Xᵢ ↦ Xᵢ + sᵢ`, `X₀ ↦ X₀ + g.shift 0`, `XᵢXⱼ ↦ XᵢXⱼ + sⱼ Xᵢ + sᵢ Xⱼ + sᵢ sⱼ`;
* `Ψ, Ψ², Ψ³ ↦` themselves, `ΨXᵢ ↦ ΨXᵢ + sᵢ Ψ`, `Ψ²Xᵢ ↦ Ψ²Xᵢ + sᵢ Ψ²`;
* `I(Ψ) ↦ I(Ψ) + cPsi + Σ cPsiGrad i Xᵢ`, `I(Ψ²) ↦ I(Ψ²) + cPsiSq`,
  `I(Ψ³) ↦ I(Ψ³) + cPsiCube`;
* `I(Ψ)Ψ ↦ I(Ψ)Ψ + cPsi Ψ + Σ cPsiGrad i ΨXᵢ`,
  `I(Ψ)Ψ² ↦ I(Ψ)Ψ² + cPsi Ψ² + Σ cPsiGrad i Ψ²Xᵢ`;
* `I(Ψ²)Ψ ↦ I(Ψ²)Ψ + cPsiSq Ψ`, `I(Ψ²)Ψ² ↦ I(Ψ²)Ψ² + cPsiSq Ψ²`;
* `I(Ψ³)Ψ ↦ I(Ψ³)Ψ + cPsiCube Ψ`, `I(Ψ³)Ψ² ↦ I(Ψ³)Ψ² + cPsiCube Ψ²`;
* `I(Ψ³)² ↦ I(Ψ³)² + 2 cPsiCube I(Ψ³) + cPsiCube²`.

These are the entries of `D.canonicalGamma z z'` with `g = D.canonicalGammaParameter z z'`
(definitionally); the parameters are computed in `Phi43.BPHZ.GammaEntryParameters`.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

open RegularityStructures

section Entries

variable (g : G)

theorem structureGroupMap_basis_noise_eq :
    structureGroupMap g (basis .noise) = basis .noise := by
  simp [structureGroupMap_basis, structureBasisAction, primitiveAction]

theorem structureGroupMap_basis_x_eq (i : Fin 3) :
    structureGroupMap g (basis (.x i)) = basis (.x i) + g.shift i.succ • basis .one := by
  simp [structureGroupMap_basis, structureBasisAction, primitiveAction]

theorem structureGroupMap_basis_psi_eq :
    structureGroupMap g (basis .psi) = basis .psi := by
  simp [structureGroupMap_basis, structureBasisAction, primitiveAction]

theorem structureGroupMap_basis_psiSq_eq :
    structureGroupMap g (basis .psiSq) = basis .psiSq := by
  simp [structureGroupMap_basis, structureBasisAction, primitiveAction, multiply_basis,
    basisProduct, productSymbol]

theorem structureGroupMap_basis_psiCube_eq :
    structureGroupMap g (basis .psiCube) = basis .psiCube := by
  simp [structureGroupMap_basis, structureBasisAction, primitiveAction, multiply_basis,
    basisProduct, productSymbol]

theorem structureGroupMap_basis_psiX_eq (i : Fin 3) :
    structureGroupMap g (basis (.psiX i)) =
      basis (.psiX i) + g.shift i.succ • basis .psi := by
  simp [structureGroupMap_basis, structureBasisAction, primitiveAction, multiply_add_right,
    multiply_smul_right, multiply_basis, basisProduct, productSymbol]

theorem structureGroupMap_basis_psiSqX_eq (i : Fin 3) :
    structureGroupMap g (basis (.psiSqX i)) =
      basis (.psiSqX i) + g.shift i.succ • basis .psiSq := by
  simp [structureGroupMap_basis, structureBasisAction, primitiveAction, multiply_add_left,
    multiply_smul_left, multiply_basis, basisProduct, productSymbol]

theorem structureGroupMap_basis_iPsiSq_eq :
    structureGroupMap g (basis .iPsiSq) = basis .iPsiSq + g.cPsiSq • basis .one := by
  simp [structureGroupMap_basis, structureBasisAction, primitiveAction]

theorem structureGroupMap_basis_iPsiCube_eq :
    structureGroupMap g (basis .iPsiCube) = basis .iPsiCube + g.cPsiCube • basis .one := by
  simp [structureGroupMap_basis, structureBasisAction, primitiveAction]

theorem structureGroupMap_basis_iPsiPsi_eq :
    structureGroupMap g (basis .iPsiPsi) =
      basis .iPsiPsi + g.cPsi • basis .psi + ∑ i : Fin 3, g.cPsiGrad i • basis (.psiX i) := by
  simp [structureGroupMap_basis, structureBasisAction, integratedPsiProductAction]

theorem structureGroupMap_basis_iPsiPsiSq_eq :
    structureGroupMap g (basis .iPsiPsiSq) =
      basis .iPsiPsiSq + g.cPsi • basis .psiSq +
        ∑ i : Fin 3, g.cPsiGrad i • basis (.psiSqX i) := by
  simp [structureGroupMap_basis, structureBasisAction, integratedPsiProductAction]

theorem structureGroupMap_basis_iPsiSqPsi_eq :
    structureGroupMap g (basis .iPsiSqPsi) = basis .iPsiSqPsi + g.cPsiSq • basis .psi := by
  simp [structureGroupMap_basis, structureBasisAction, primitiveAction, multiply_add_left,
    multiply_smul_left, multiply_basis, basisProduct, productSymbol]

theorem structureGroupMap_basis_iPsiSqPsiSq_eq :
    structureGroupMap g (basis .iPsiSqPsiSq) =
      basis .iPsiSqPsiSq + g.cPsiSq • basis .psiSq := by
  simp [structureGroupMap_basis, structureBasisAction, primitiveAction, multiply_add_left,
    multiply_smul_left, multiply_basis, basisProduct, productSymbol]

theorem structureGroupMap_basis_iPsiCubePsi_eq :
    structureGroupMap g (basis .iPsiCubePsi) =
      basis .iPsiCubePsi + g.cPsiCube • basis .psi := by
  simp [structureGroupMap_basis, structureBasisAction, primitiveAction, multiply_add_left,
    multiply_smul_left, multiply_basis, basisProduct, productSymbol]

theorem structureGroupMap_basis_iPsiCubePsiSq_eq :
    structureGroupMap g (basis .iPsiCubePsiSq) =
      basis .iPsiCubePsiSq + g.cPsiCube • basis .psiSq := by
  simp [structureGroupMap_basis, structureBasisAction, primitiveAction, multiply_add_left,
    multiply_smul_left, multiply_basis, basisProduct, productSymbol]

theorem structureGroupMap_basis_iPsiCubeSq_eq :
    structureGroupMap g (basis .iPsiCubeSq) =
      basis .iPsiCubeSq + (2 * g.cPsiCube) • basis .iPsiCube +
        (g.cPsiCube * g.cPsiCube) • basis .one := by
  simp [structureGroupMap_basis, structureBasisAction, primitiveAction, multiply_add_left,
    multiply_add_right, multiply_smul_left, multiply_smul_right, multiply_basis, basisProduct,
    productSymbol, smul_smul]
  module

end Entries

end RegularityStructures.Phi43

end
