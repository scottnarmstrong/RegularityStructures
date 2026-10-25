/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.RenormalisedExtensionTensorIntegration
public import Phi43.BPHZ.PositiveTreeFormulas
public import Phi43.Structure.CanonicalKernelHairer

/-!
# The extension `Π` on `I(Ψ²)` is the renormalised `Π`

The analogue of `renormalisedExtensionPi_tensor_iPsiCube` for `I(Ψ²)`, which the renormalisation
map `M` fixes.
-/

public section

namespace RegularityStructures.Phi43

open RegularityStructures

theorem renormalisedExtensionPi_tensor_iPsiSq (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (c : RenormalisationConstants) (x : ParabolicSpace) :
    (hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi c x (basis .iPsiSq) =
      (hairerCanonicalData (κ := κ) N noise).renormalisedPi c x (basis .iPsiSq) := by
  let D := hairerCanonicalData (κ := κ) N noise
  change D.renormalisedExtensionPi c x (basis .iPsiSq) = D.renormalisedPi c x (basis .iPsiSq)
  rw [CanonicalData.renormalisedPi_basis_iPsiSq_eq]
  have hk : κ.1 < (1 / 16 : ℝ) := κ.2.2
  have h0 : 0 < homogeneity κ .iPsiSq := by simp only [homogeneity]; linarith
  have h1 : ¬ 1 < homogeneity κ .iPsiSq := by
    simp only [homogeneity]; linarith [kappa_pos κ]
  funext y
  rw [CanonicalData.integrate_eq_of_pos_of_not_gt_one D h0 h1]
  simp [CanonicalData.renormalisedExtensionPi, CanonicalData.renormalisedExtensionCharacter,
    structureGroupMap_basis, structureBasisAction, primitiveAction,
    CanonicalData.renormalisedExtensionGlobalPi_basis,
    CanonicalData.renormalisedExtensionGlobalBasis, CanonicalData.globalPiBasis,
    CanonicalData.canonicalCharacter]
  simp [CanonicalData.globalIPsiSq, CanonicalData.localPsiSq_eq_globalPsiSq]
  ring

end RegularityStructures.Phi43

end
