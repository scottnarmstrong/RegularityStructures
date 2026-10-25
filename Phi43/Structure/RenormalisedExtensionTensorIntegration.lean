/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.RenormalisedExtensionAlgebra
import Mathlib.Tactic.Ring
public import Phi43.Structure.CanonicalKernelHairer

/-!
# Source tensor comparison for the integrated cubic

The X_i tensor J_i(Psi) terms in Delta^M are essential here. They turn
the Taylor-subtracted I(Psi) counterterm into the constant-Taylor correction
of the integrated cubic [Hai14, (8.34), (9.3)–(9.5)].
-/

public noncomputable section

namespace RegularityStructures.Phi43

namespace CanonicalData

variable {κ : Kappa} (D : CanonicalData κ)

/-- Tensoring with the positive unit preserves the actual canonical lift. -/
theorem canonicalPiTensor_unit (z : ParabolicSpace) (v : T) :
    D.canonicalPiTensor z (tensorOf v (plusBasis .one)) = D.canonicalPi z v := by
  have hlin : (D.canonicalPiTensor z).comp
      (Finsupp.bilinearCombination ℝ ℝ (fun τ : Symbol =>
        Finsupp.single τ (plusBasis .one))) = D.canonicalPi z := by
    apply Finsupp.lhom_ext
    intro τ r
    rw [← Finsupp.smul_single_one]
    simp only [LinearMap.comp_apply, map_smul]
    rw [show (Finsupp.bilinearCombination ℝ ℝ (fun σ : Symbol =>
        Finsupp.single σ (plusBasis .one))) (Finsupp.single τ 1) =
        tensorBasis τ .one by simp [tensorBasis, plusBasis]]
    rw [canonicalPiTensor, LinearMap.comp_apply]
    change r • D.canonicalPi z
        (deltaCharacter (D.canonicalCharacter z) (tensorBasis τ .one)) = _
    rw [deltaCharacter_tensorBasis, map_smul]
    simp [plusCharacter, plusCharacterBasis, plusBasis, basis]
  exact LinearMap.congr_fun hlin v

end CanonicalData

theorem renormalisedExtensionPi_tensor_iPsiCube (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (c : RenormalisationConstants) (x : ParabolicSpace) :
    (hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi c x (basis .iPsiCube) =
      (hairerCanonicalData (κ := κ) N noise).renormalisedPi c x (basis .iPsiCube) := by
  let D := hairerCanonicalData (κ := κ) N noise
  change D.renormalisedExtensionPi c x (basis .iPsiCube) =
    D.renormalisedPi c x (basis .iPsiCube)
  have hk : κ.1 < (1 / 16 : ℝ) := κ.2.2
  have hI : 0 < homogeneity κ .iPsiCube := by
    simp only [homogeneity]
    linarith
  have hI' : ¬ 1 < homogeneity κ .iPsiCube := by
    simp only [homogeneity]
    linarith [kappa_pos κ]
  have hJ : 0 < homogeneity κ .iPsi := by
    simp only [homogeneity]
    linarith
  have hJ' : 1 < homogeneity κ .iPsi := by
    simp only [homogeneity]
    linarith
  rw [CanonicalData.renormalisedPi_apply, deltaM_basis]
  simp only [deltaMBasis, map_add, map_smul, map_sum,
    CanonicalData.canonicalPiTensor_unit, CanonicalData.canonicalPiTensor_basis]
  simp only [M_basis, contraction_basis, L1BasisAction, L2BasisAction,
    map_smul, map_zero, smul_zero, sub_zero, map_add]
  funext y
  simp only [CanonicalData.renormalisedExtensionPi, LinearMap.comp_apply,
    structureGroupMap_basis, structureBasisAction, primitiveAction,
    CanonicalData.renormalisedExtensionCharacter, map_add, map_smul,
    CanonicalData.renormalisedExtensionGlobalPi_basis,
    CanonicalData.renormalisedExtensionGlobalBasis, CanonicalData.renormalisedExtensionPotential,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_apply, CanonicalData.canonicalPi_basis, CanonicalData.localPiBasis,
    plusCharacter_basis, plusCharacterBasis]
  simp [CanonicalData.localIPsiCube, CanonicalData.localIPsi, CanonicalData.integrate,
    CanonicalKernel.taylorPolynomial, hI, hI', hJ, hJ', CanonicalData.globalPiBasis,
    CanonicalData.canonicalCharacter, CanonicalData.canonicalCPsiGrad,
    CanonicalData.localPsi_eq_globalPsi, CanonicalData.localPsiCube_eq_globalPsiCube,
    CanonicalData.globalIPsi, CanonicalData.globalIPsiCube, CanonicalKernel.convolution,
    CanonicalData.relCoord, D, hairerCanonicalData, hairerCanonicalKernel]
  ring

end RegularityStructures.Phi43

end
