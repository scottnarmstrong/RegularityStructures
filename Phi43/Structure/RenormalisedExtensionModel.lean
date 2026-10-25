/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.RenormalisedExtensionRealisation
public import Phi43.Structure.RenormalisedExtensionContinuity
public import Phi43.Structure.CanonicalGrowthPremise
public import RegularityStructures.Abstract.Model

/-!
# Actual abstract Model of the corrected smooth extension

The pi field is Q applied to the explicitly defined corrected functions
on the entire retained space. This supplies the abstract Model fields;
source tensor agreement on H0, compact analytic bounds and admissibility
are separate obligations before claiming Hairer's Theorem 8.44.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- Distributional model of the explicit smooth extension under polynomial
growth of the noise. Source identification and analytic bounds are separate. -/
def renormalisedSmoothExtensionModel (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (hf : PolyBounded noise.zeta) (c : RenormalisationConstants) :
    Model (phi43RegularityStructure κ) parabolicSemigroup where
  pi x := (renormalisedExtensionDistributionLinear N (κ := κ) noise hf c x).comp
    phi43CoordinateEquiv.symm.toLinearMap
  gamma x y :=
    ⟨phi43StructureGroupElement
      ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGammaParameter c x y),
      phi43RegularityStructure_group_mem κ _⟩
  pi_gamma x y a := by
    simp only [LinearMap.comp_apply, phi43StructureGroupElement,
      LinearMap.GeneralLinearGroup.coe_ofLinearEquiv, phi43StructureGroupEquiv,
      LinearEquiv.trans_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      structureGroupLinearEquiv_apply]
    change renormalisedExtensionDistribution N (κ := κ) noise hf c x
      ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGamma c x y
        (phi43CoordinateEquiv.symm a)) =
      renormalisedExtensionDistribution N (κ := κ) noise hf c y (phi43CoordinateEquiv.symm a)
    exact renormalisedExtensionDistribution_covariance N noise hf c x y _
  gamma_self x := by
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro a
    change phi43CoordinateEquiv
      ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGamma c x x
        (phi43CoordinateEquiv.symm a)) = a
    rw [CanonicalData.renormalisedExtensionGamma_self]
    exact phi43CoordinateEquiv.apply_symm_apply a
  gamma_mul x y z := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Units.val_mul]
    apply LinearMap.ext
    intro a
    change
      (phi43StructureGroupElement
        ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGammaParameter c x y) :
          (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ))
        ((phi43StructureGroupElement
          ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGammaParameter c y z) :
            (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ)) a) = _
    simp only [phi43StructureGroupElement, LinearMap.GeneralLinearGroup.coe_ofLinearEquiv,
      phi43StructureGroupEquiv, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_apply, structureGroupLinearEquiv_apply]
    change phi43CoordinateEquiv
      ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGamma c x y
        ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGamma c y z
          (phi43CoordinateEquiv.symm a))) =
      phi43CoordinateEquiv
        ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGamma c x z
          (phi43CoordinateEquiv.symm a))
    exact congrArg phi43CoordinateEquiv (LinearMap.congr_fun
      (CanonicalData.renormalisedExtensionGamma_comp _ c x y z) (phi43CoordinateEquiv.symm a))
  measurable_diag τ t ht := by
    change Measurable (fun x =>
      (renormalisedExtensionDistribution N (κ := κ) noise hf c x
        (phi43CoordinateEquiv.symm (Pi.single τ 1)) : ℝ → ParabolicSpace → ℝ) t x)
    have he : phi43CoordinateEquiv.symm (Pi.single τ 1) = basis τ := by
      apply phi43CoordinateEquiv.injective
      simp [phi43CoordinateEquiv_basis]
    simp_rw [he, renormalisedExtensionDistribution_reg_eq_sum N noise hf c _ _ ht]
    exact Finset.measurable_sum _ fun σ _ =>
      (continuous_renormalisedExtensionStructureGroup_coeff N noise c τ σ).measurable.mul
        (parabolicSemigroup.measurable_apply t
          (renormalisedExtensionGlobalBasis_growth N κ noise hf c σ).1)
  measurable_pi x τ t ht := by
    change Measurable (fun z =>
      (renormalisedExtensionDistribution N (κ := κ) noise hf c x
        (phi43CoordinateEquiv.symm (Pi.single τ 1)) : ℝ → ParabolicSpace → ℝ) t z)
    change Measurable (fun z => if 0 < t then parabolicSemigroup.apply t
      ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi c x
        (phi43CoordinateEquiv.symm (Pi.single τ 1))) z else 0)
    simp only [ht, ite_true]
    exact parabolicSemigroup.measurable_apply t (renormalisedExtensionPi_growth N noise hf c x _).1

/-- Genuine abstract Model of the explicit corrected smooth extension.
Analytic bounds and identification with Hairer's tensor action are not
inputs and are not asserted by this constructor. -/
def canonicalRenormalisedModel (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (C : ℝ) (p : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ C * (1 + parabolicNorm z) ^ p)
    (c : RenormalisationConstants) :
    Model (phi43RegularityStructure κ) parabolicSemigroup :=
  renormalisedSmoothExtensionModel N κ noise
    (canonicalNoise_polyBounded_of_derivatives noise C p hg) c

/-- The Model regularises precisely the explicit corrected function. -/
theorem canonicalRenormalisedModel_regPi (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (C : ℝ) (p : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ C * (1 + parabolicNorm z) ^ p)
    (c : RenormalisationConstants) (x : ParabolicSpace) (a : Symbol → ℝ)
    {t : ℝ} (ht : 0 < t) (z : ParabolicSpace) :
    (canonicalRenormalisedModel N κ noise C p hg c).regPi x a t z =
      parabolicSemigroup.apply t
        ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi c x
          (phi43CoordinateEquiv.symm a)) z := by
  change (if 0 < t then _ else 0) = _
  simp only [ht, ite_true, LinearEquiv.coe_coe]

end RegularityStructures.Phi43

end
