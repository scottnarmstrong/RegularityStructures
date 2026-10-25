/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.RenormalisedExtensionTensorIntegration
import Mathlib.Tactic.Ring
public import Phi43.Structure.CanonicalKernelHairer

/-!
# Explicit based renormalised tree functions

The integrated cubic uses constant Taylor subtraction of its corrected
potential, while I(Psi) has its first spatial Taylor subtraction. These
are the concrete smooth forms underlying Hairer [Hai14, (9.3)–(9.5)].
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43.CanonicalData

variable {κ : Kappa} (D : CanonicalData κ)

/-- The based corrected cubic potential. -/
def renormalisedBasedCube (c : RenormalisationConstants) (x y : ParabolicSpace) : ℝ :=
  D.localIPsiCube x y - 3 * C₁ c * (D.globalIPsi y - D.globalIPsi x)

/-- Literal formulas for the based corrected smooth functions. -/
def renormalisedBasedBasis (c : RenormalisationConstants) (x : ParabolicSpace) :
    Symbol → ParabolicSpace → ℝ
  | .psiSq => fun y => D.globalPsiSq y - C₁ c
  | .psiCube => fun y => D.globalPsiCube y - 3 * C₁ c * D.globalPsi y
  | .psiSqX i => fun y => (D.globalPsiSq y - C₁ c) * relCoord x y i.succ
  | .iPsiCube => D.renormalisedBasedCube c x
  | .iPsiPsiSq => fun y => D.localIPsi x y * (D.globalPsiSq y - C₁ c)
  | .iPsiSqPsiSq => fun y => D.localIPsiSq x y * (D.globalPsiSq y - C₁ c) - C₂ c
  | .iPsiCubePsi => fun y => D.renormalisedBasedCube c x y * D.globalPsi y
  | .iPsiCubePsiSq => fun y =>
      D.renormalisedBasedCube c x y * (D.globalPsiSq y - C₁ c) - 3 * C₂ c * D.globalPsi y
  | .iPsiCubeSq => fun y => D.renormalisedBasedCube c x y * D.renormalisedBasedCube c x y
  | τ => D.localPiBasis x τ

end RegularityStructures.Phi43.CanonicalData

end

public noncomputable section

namespace RegularityStructures.Phi43

theorem renormalisedExtensionPi_basis_form (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (c : RenormalisationConstants) (x : ParabolicSpace) (τ : Symbol) :
    (hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi c x (basis τ) =
      (hairerCanonicalData (κ := κ) N noise).renormalisedBasedBasis c x τ := by
  let D := hairerCanonicalData (κ := κ) N noise
  have hk : κ.1 < (1 / 16 : ℝ) := κ.2.2
  have hp : 0 < κ.1 := κ.2.1
  have hI : 0 < homogeneity κ .iPsiCube := by simp only [homogeneity]; linarith
  have hI' : ¬ 1 < homogeneity κ .iPsiCube := by simp only [homogeneity]; linarith
  have hS : 0 < homogeneity κ .iPsiSq := by simp only [homogeneity]; linarith
  have hS' : ¬ 1 < homogeneity κ .iPsiSq := by simp only [homogeneity]; linarith
  have hJ : 0 < homogeneity κ .iPsi := by simp only [homogeneity]; linarith
  have hJ' : 1 < homogeneity κ .iPsi := by simp only [homogeneity]; linarith
  have hK (f : ParabolicSpace → ℝ) : D.kernel.convolutionOp f = D.kernel.taylorConstant f := rfl
  change D.renormalisedExtensionPi c x (basis τ) = D.renormalisedBasedBasis c x τ
  funext y
  cases τ
  case xMul p =>
    induction p using Sym2.inductionOn with
    | _ i j =>
      simp [CanonicalData.renormalisedExtensionPi, LinearMap.comp_apply,
        structureGroupMap_basis, structureBasisAction, xMulAction_mk, primitiveAction,
        multiply_add_left, multiply_add_right, multiply_smul_left, multiply_smul_right,
        multiply_basis, basisProduct, productSymbol,
        CanonicalData.renormalisedExtensionGlobalPi_basis, CanonicalData.renormalisedExtensionGlobalBasis,
        CanonicalData.renormalisedExtensionCharacter, CanonicalData.globalPiBasis,
        CanonicalData.renormalisedBasedBasis, CanonicalData.localPiBasis,
        CanonicalData.globalPolynomialQuadratic, CanonicalData.localPolynomialQuadratic,
        CanonicalData.relCoord, CanonicalData.canonicalCharacter, CanonicalData.canonicalShift]
      ring
  all_goals
    simp only [CanonicalData.renormalisedExtensionPi, LinearMap.comp_apply,
      structureGroupMap_basis, structureBasisAction, primitiveAction, integratedPsiProductAction,
      multiply_add_left, multiply_add_right, multiply_smul_left, multiply_smul_right,
      multiply_basis, basisProduct, productSymbol, map_add, map_smul, map_sum,
      CanonicalData.renormalisedExtensionGlobalPi_basis, CanonicalData.renormalisedExtensionGlobalBasis,
      CanonicalData.renormalisedExtensionCharacter, CanonicalData.renormalisedExtensionPotential,
      CanonicalData.renormalisedBasedBasis, CanonicalData.renormalisedBasedCube,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
      CanonicalData.globalPiBasis, CanonicalData.localPiBasis]
  all_goals
    simp [CanonicalData.localIPsiCube, CanonicalData.localIPsiSq, CanonicalData.localIPsi,
      CanonicalData.localIPsiPsi, CanonicalData.localIPsiSqPsi, CanonicalData.integrate,
      CanonicalKernel.taylorPolynomial, hI, hI', hS, hS', hJ, hJ',
      CanonicalData.canonicalCharacter, CanonicalData.canonicalCPsi, CanonicalData.canonicalCPsiGrad,
      CanonicalData.localPsi_eq_globalPsi, CanonicalData.localPsiSq_eq_globalPsiSq,
      CanonicalData.localPsiCube_eq_globalPsiCube, CanonicalData.globalIPsi,
      CanonicalData.globalIPsiSq, CanonicalData.globalIPsiCube, CanonicalKernel.convolution, hK,
      CanonicalData.globalPsiX, CanonicalData.globalIPsiPsi,
      CanonicalData.globalIPsiSqPsi, CanonicalData.localPsiX,
      CanonicalData.relCoord, CanonicalData.canonicalShift]
  all_goals try simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  all_goals ring

end RegularityStructures.Phi43

end
