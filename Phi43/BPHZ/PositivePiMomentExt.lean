/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.PositiveTreeFormulasBridge
public import Phi43.BPHZ.PositiveMomentGammaSq
import Mathlib.Tactic

/-!
# The extension `Π` on the positive-degree symbols

For `D : CanonicalData κ`, constants `c` and a base point `x`, the explicitly defined smooth
extension `D.renormalisedExtensionPi c x` of Hairer's renormalised lift (the one realised by
`canonicalRenormalisedModel`) satisfies on the positive-degree symbols

* `Π_x I(Ψ) = ` the renormalised `Π_x I(Ψ)` (`renormalisedExtensionPi_tensor_iPsi`);
* `Π_x ΨXᵢ = Ψ (yᵢ - xᵢ)`, `Π_x I(Ψ)Ψ = Π_x I(Ψ) Ψ`, `Π_x I(Ψ)Ψ² = Π_x I(Ψ) (Ψ² - C₁)`,
  `Π_x I(Ψ²)Ψ = Π_x I(Ψ²) Ψ`, `Π_x I(Ψ³)² = (Π_x I(Ψ³))²`.

The last one differs from the corresponding row of `renormalisedPi`: the extension uses the actual
square of the corrected potential.
-/

public section

namespace RegularityStructures.Phi43

open RegularityStructures

variable {κ : Kappa} (D : CanonicalData κ) (c : RenormalisationConstants) (x : ParabolicSpace)

theorem renormalisedExtensionPi_tensor_iPsi :
    D.renormalisedExtensionPi c x (basis .iPsi) = D.renormalisedPi c x (basis .iPsi) := by
  have hk : κ.1 < (1 / 16 : ℝ) := κ.2.2
  have hJ : 0 < homogeneity κ .iPsi := by
    simp only [homogeneity]
    linarith
  have hJ' : 1 < homogeneity κ .iPsi := by
    simp only [homogeneity]
    linarith
  rw [CanonicalData.renormalisedPi_basis_iPsi_eq]
  funext y
  simp [CanonicalData.renormalisedExtensionPi, CanonicalData.renormalisedExtensionCharacter,
    structureGroupMap_basis, structureBasisAction, primitiveAction,
    CanonicalData.renormalisedExtensionGlobalPi_basis,
    CanonicalData.renormalisedExtensionGlobalBasis, CanonicalData.globalPiBasis,
    CanonicalData.canonicalCharacter, CanonicalData.integrate, CanonicalKernel.taylorPolynomial,
    hJ, hJ', CanonicalData.canonicalCPsi, CanonicalData.canonicalCPsiGrad,
    CanonicalData.canonicalShift, CanonicalData.localPsi_eq_globalPsi,
    CanonicalData.globalIPsi, mul_sub, Finset.sum_sub_distrib]
  simp only [mul_comm]
  ring

theorem renormalisedExtensionPi_psiX (i : Fin 3) (y : ParabolicSpace) :
    D.renormalisedExtensionPi c x (basis (.psiX i)) y =
      D.globalPsi y * (parabolicCoords y i.succ - parabolicCoords x i.succ) := by
  simp [CanonicalData.renormalisedExtensionPi, CanonicalData.renormalisedExtensionCharacter,
    structureGroupMap_basis, structureBasisAction, primitiveAction, multiply_basis,
    basisProduct, productSymbol,
    CanonicalData.renormalisedExtensionGlobalPi_basis,
    CanonicalData.renormalisedExtensionGlobalBasis, CanonicalData.globalPiBasis,
    CanonicalData.canonicalCharacter, CanonicalData.canonicalShift, CanonicalData.globalPsiX]
  ring

theorem renormalisedExtensionPi_iPsiPsi (y : ParabolicSpace) :
    D.renormalisedExtensionPi c x (basis .iPsiPsi) y =
      D.renormalisedExtensionPi c x (basis .iPsi) y * D.globalPsi y := by
  simp [CanonicalData.renormalisedExtensionPi, CanonicalData.renormalisedExtensionCharacter,
    structureGroupMap_basis, structureBasisAction, primitiveAction, integratedPsiProductAction,
    CanonicalData.renormalisedExtensionGlobalPi_basis,
    CanonicalData.renormalisedExtensionGlobalBasis, CanonicalData.globalPiBasis,
    CanonicalData.canonicalCharacter, CanonicalData.globalPsiX, CanonicalData.globalIPsiPsi]
  simp only [add_mul, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

theorem renormalisedExtensionPi_iPsiPsiSq (y : ParabolicSpace) :
    D.renormalisedExtensionPi c x (basis .iPsiPsiSq) y =
      D.renormalisedExtensionPi c x (basis .iPsi) y * (D.globalPsiSq y - C₁ c) := by
  simp [CanonicalData.renormalisedExtensionPi, CanonicalData.renormalisedExtensionCharacter,
    structureGroupMap_basis, structureBasisAction, primitiveAction, integratedPsiProductAction,
    CanonicalData.renormalisedExtensionGlobalPi_basis,
    CanonicalData.renormalisedExtensionGlobalBasis, CanonicalData.globalPiBasis,
    CanonicalData.canonicalCharacter]
  simp only [add_mul, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

theorem renormalisedExtensionPi_iPsiSqPsi (y : ParabolicSpace) :
    D.renormalisedExtensionPi c x (basis .iPsiSqPsi) y =
      D.renormalisedExtensionPi c x (basis .iPsiSq) y * D.globalPsi y := by
  simp [CanonicalData.renormalisedExtensionPi, CanonicalData.renormalisedExtensionCharacter,
    structureGroupMap_basis, structureBasisAction, primitiveAction, multiply_basis,
    basisProduct, productSymbol,
    CanonicalData.renormalisedExtensionGlobalPi_basis,
    CanonicalData.renormalisedExtensionGlobalBasis, CanonicalData.globalPiBasis,
    CanonicalData.canonicalCharacter, CanonicalData.globalIPsiSqPsi]
  ring

theorem renormalisedExtensionPi_iPsiCubeSq (y : ParabolicSpace) :
    D.renormalisedExtensionPi c x (basis .iPsiCubeSq) y =
      D.renormalisedExtensionPi c x (basis .iPsiCube) y ^ 2 := by
  simp [CanonicalData.renormalisedExtensionPi, CanonicalData.renormalisedExtensionCharacter,
    structureGroupMap_basis, structureBasisAction, primitiveAction, multiply_basis,
    basisProduct, productSymbol,
    CanonicalData.renormalisedExtensionGlobalPi_basis,
    CanonicalData.renormalisedExtensionGlobalBasis, CanonicalData.globalPiBasis,
    CanonicalData.canonicalCharacter, CanonicalData.renormalisedExtensionPotential]
  ring

end RegularityStructures.Phi43

end
