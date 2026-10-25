/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.RenormalisedExtensionBasedForm
public import Phi43.Structure.RenormalisedExtensionRealisation
public import Phi43.Structure.CanonicalConvolutionLinearity
public import Phi43.Structure.CanonicalTaylorIntegrationSources

/-!
# Actual Taylor-shell realisation of the corrected smooth sources

Constant Taylor subtraction cancels the convolution of a constant source.
The cubic correction is linear under the actual convolution. These prove
the ordinary integral content of admissibility, without any model-bound
premises [Hai14, Definition 5.9, (8.20), (9.5)].
-/

public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

private theorem integrated_low (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (c : RenormalisationConstants) (x y : ParabolicSpace) (τ : Symbol)
    (hτ : τ = .psiSq ∨ τ = .psiCube) :
    (hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi c x
        (integration (basis τ)) y =
      hairerConvolution N
        ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi c x (basis τ)) y -
      hairerConvolution N
        ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi c x (basis τ)) x := by
  let D := hairerCanonicalData (κ := κ) N noise
  have hp : Continuous D.globalPsi := (canonicalGlobalPiBasis_smooth N noise .psi).continuous
  have hs : Continuous D.globalPsiSq := (canonicalGlobalPiBasis_smooth N noise .psiSq).continuous
  have hc : Continuous D.globalPsiCube := (canonicalGlobalPiBasis_smooth N noise .psiCube).continuous
  have hk : κ.1 < (1 / 16 : ℝ) := κ.2.2
  have hk0 : 0 < κ.1 := κ.2.1
  rcases hτ with rfl | rfl
  · have h0 : 0 < homogeneity κ .iPsiSq := by simp only [homogeneity]; linarith
    have h1 : ¬ 1 < homogeneity κ .iPsiSq := by simp only [homogeneity]; linarith
    simp only [integration_basis, integrationBasisAction, renormalisedExtensionPi_basis_form]
    change D.localIPsiSq x y =
      hairerConvolution N (fun w => D.globalPsiSq w - C₁ c) y -
      hairerConvolution N (fun w => D.globalPsiSq w - C₁ c) x
    rw [hairerConvolution_sub_continuous N hs continuous_const,
      hairerConvolution_sub_continuous N hs continuous_const]
    simp only [hairerConvolution_const_value]
    have hl : D.localIPsiSq x y =
        hairerConvolution N D.globalPsiSq y - hairerConvolution N D.globalPsiSq x := by
      simp only [CanonicalData.localIPsiSq, CanonicalData.integrate,
        CanonicalData.localPsiSq_eq_globalPsiSq, CanonicalKernel.taylorPolynomial,
        h0, h1, ite_true, ite_false, add_zero]
      rfl
    rw [hl]
    ring
  · have h0 : 0 < homogeneity κ .iPsiCube := by simp only [homogeneity]; linarith
    have h1 : ¬ 1 < homogeneity κ .iPsiCube := by simp only [homogeneity]; linarith
    simp only [integration_basis, integrationBasisAction, renormalisedExtensionPi_basis_form]
    change D.renormalisedBasedCube c x y =
      hairerConvolution N (fun w => D.globalPsiCube w - 3 * C₁ c * D.globalPsi w) y -
      hairerConvolution N (fun w => D.globalPsiCube w - 3 * C₁ c * D.globalPsi w) x
    have hprod : Continuous (fun w => 3 * C₁ c * D.globalPsi w) := continuous_const.mul hp
    rw [hairerConvolution_sub_continuous N hc hprod,
      hairerConvolution_sub_continuous N hc hprod]
    simp only [hairerConvolution_mul_const, CanonicalData.renormalisedBasedCube]
    have hl : D.localIPsiCube x y =
        hairerConvolution N D.globalPsiCube y - hairerConvolution N D.globalPsiCube x := by
      simp only [CanonicalData.localIPsiCube, CanonicalData.integrate,
        CanonicalData.localPsiCube_eq_globalPsiCube, CanonicalKernel.taylorPolynomial,
        h0, h1, ite_true, ite_false, add_zero]
      rfl
    rw [hl]
    change (_ - _) - 3 * C₁ c *
      (hairerConvolution N D.globalPsi y - hairerConvolution N D.globalPsi x) = _
    ring

/-- Ordinary Taylor shell integration on all four retained sources. -/
theorem renormalisedExtension_integration_shell_sum_sources (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (c : RenormalisationConstants) (x y : ParabolicSpace)
    (τ : Symbol) (hτ : τ = .noise ∨ τ = .psi ∨ τ = .psiSq ∨ τ = .psiCube) :
    (hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi c x
        (integration (basis τ)) y =
      ∑' n : ℕ, ∫ w,
        (hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi c x (basis τ) w *
          taylorKernel (annKernel0C N) n (homogeneity κ τ + 2) x y w := by
  rcases hτ with rfl | rfl | hτ
  · simpa only [integration_basis, integrationBasisAction, renormalisedExtensionPi_basis_form,
      CanonicalData.renormalisedBasedBasis, CanonicalData.canonicalPi_basis] using
      canonicalPi_integration_shell_sum_noise N κ noise x y
  · simpa only [integration_basis, integrationBasisAction, renormalisedExtensionPi_basis_form,
      CanonicalData.renormalisedBasedBasis, CanonicalData.canonicalPi_basis] using
      canonicalPi_integration_shell_sum_psi N κ noise x y
  · rw [integrated_low N κ noise c x y τ hτ]
    apply hairerConvolution_eq_tsum_taylorKernel_low N
      (renormalisedExtensionPi_smooth N noise c x (basis τ)).continuous
    · have hk : κ.1 < (1 / 16 : ℝ) := κ.2.2
      rcases hτ with rfl | rfl <;> simp only [homogeneity] <;> linarith
    · have hk0 : 0 < κ.1 := κ.2.1
      rcases hτ with rfl | rfl <;> simp only [homogeneity] <;> linarith

end RegularityStructures.Phi43

end
