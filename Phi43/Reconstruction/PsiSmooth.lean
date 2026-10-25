/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Identification.Evaluate
public import Phi43.Structure.CanonicalSmoothConvolution
public import Phi43.Structure.CanonicalSpatialTranslationKernel
public import Phi43.Potential.DerivHyp
public import Phi43.Inhomogeneity.DuhamelField

/-!
# The potential `Ψ = K ∗ ζ` is smooth and spatially periodic

`phi43PsiAt N κ noise C = hairerConvolution N noise.zeta` (the `Ψ`-coordinate of the base
functions on the diagonal); it is smooth (`contDiff_hairerConvolution`) and spatially periodic
(`hairerConvolution_translate_of_periodic`), i.e. `PerSmooth` (`perSmooth_phi43PsiAt`).
-/

public section

namespace RegularityStructures.Phi43

private theorem diag_eq' (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (C : RenormalisationConstants) (x : ParabolicSpace) (τ : Symbol) (hτ : τ ∈ fMinus) :
    phi43BaseFunctions N κ noise C x τ x =
      (hairerCanonicalData (κ := κ) N noise).renormalisedBasedBasis C x τ x := by
  rw [phi43BaseFunctions_of_mem_fMinus N κ noise C hτ, renormalisedExtensionPi_basis_form]

theorem phi43PsiAt_eq_globalPsi (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (C : RenormalisationConstants) (x : ParabolicSpace) :
    phi43PsiAt N κ noise C x = (hairerCanonicalData (κ := κ) N noise).globalPsi x := by
  have h := diag_eq' N κ noise C x .psi (by simp [mem_fMinus_iff_isFMinus, isFMinus])
  rw [← phi43BaseFunctions_diag_psi N κ noise C x, h]
  simp [CanonicalData.renormalisedBasedBasis, CanonicalData.localPiBasis,
    CanonicalData.localPsi_eq_globalPsi]

theorem phi43PsiAt_eq (N : ℕ) (κ : Kappa) (noise : CanonicalNoise) (C : RenormalisationConstants) :
    phi43PsiAt N κ noise C = hairerConvolution N noise.zeta := by
  funext x
  rw [phi43PsiAt_eq_globalPsi]
  rfl

theorem perSmooth_phi43PsiAt (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (C : RenormalisationConstants) :
    Inhomogeneity.PerSmooth (phi43PsiAt N κ noise C) := by
  rw [phi43PsiAt_eq]
  refine Potential.perSmooth_of_integer_periodic (contDiff_hairerConvolution N noise.smooth) ?_
  intro n z
  have e : ∀ w : ParabolicSpace, w + ((0 : ℝ), fun i => (n i : ℝ)) =
      (w.1, fun i => w.2 i + (n i : ℝ)) := fun w => Prod.ext (by simp) (by funext i; simp)
  have := hairerConvolution_translate_of_periodic N noise.zeta (0, fun i => (n i : ℝ))
    (fun w => by rw [e]; exact noise.periodic n w) z
  rwa [e] at this

end RegularityStructures.Phi43

end
