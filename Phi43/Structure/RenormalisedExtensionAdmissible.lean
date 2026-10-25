/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.RenormalisedExtensionTensorModel
public import Phi43.Structure.RenormalisedTaylorSources
import RegularityStructures.Abstract.Singular.TwoModel.CoeffLinear
public import Phi43.Structure.CanonicalSmoothPolynomial
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Abstract.Profile.Realising

/-!
# Causal admissibility of the actual corrected smooth Model

Pairings of the actual Q-distributions are ordinary integrals. The proved
Taylor-shell identities give Definition 5.9, including polynomial
compatibility, with no analytic-bound certificate. Source: Hairer
[Hai14, Definition 5.9, (8.20), (9.5), Theorem 8.44].
-/

public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

private theorem coord_symm_single (τ : Symbol) :
    phi43CoordinateEquiv.symm (Pi.single τ 1) = basis τ := by
  apply phi43CoordinateEquiv.injective
  simp [phi43CoordinateEquiv_basis]

theorem canonicalRenormalisedModel_pairing_basis (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (Cg : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
    (C : RenormalisationConstants) (x : ParabolicSpace) (τ : Symbol)
    {φ : ParabolicSpace → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    parabolicSemigroup.pairing
      (fun t z => (canonicalRenormalisedModel N κ noise Cg q hg C).regPi x (Pi.single τ 1) t z) φ =
      ∫ z, (hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi C x (basis τ) z * φ z := by
  change parabolicSemigroup.pairing
    (renormalisedExtensionDistribution N (κ := κ) noise
      (canonicalNoise_polyBounded_of_derivatives noise Cg q hg) C x
      (phi43CoordinateEquiv.symm (Pi.single τ 1))) φ = _
  rw [coord_symm_single]
  exact canonicalSmoothReg_pairing (renormalisedExtensionPi_smooth N noise C x (basis τ)).continuous
    (renormalisedExtensionPi_growth N noise
      (canonicalNoise_polyBounded_of_derivatives noise Cg q hg) C x (basis τ)) hφ hφc

private theorem poly_same (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (C : RenormalisationConstants) (x : ParabolicSpace) (k : PolyIndex 2) :
    (hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi C x (basis (phi43PolyEmb k)) =
      (hairerCanonicalData (κ := κ) N noise).canonicalPi x (basis (phi43PolyEmb k)) := by
  rw [renormalisedExtensionPi_basis_form, CanonicalData.canonicalPi_basis]
  rcases polyIndex_two_cases k with hk | hk | hk | hk <;>
    simp [phi43PolyEmb, hk, CanonicalData.renormalisedBasedBasis]

private theorem poly_compatible (N : ℕ) (κ : Kappa) (noise : CanonicalNoise) (Cg : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
    (C : RenormalisationConstants) :
    (canonicalRenormalisedModel N κ noise Cg q hg C).IsPolyCompatible (phi43PolynomialSector κ) := by
  intro x k t z
  change (if 0 < t then parabolicSemigroup.apply t
    ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi C x
      (phi43CoordinateEquiv.symm (Pi.single (phi43PolyEmb k) 1))) z else 0) = _
  rw [coord_symm_single, poly_same, canonicalPi_polynomial]
  rfl

private theorem realGerm_sources (N : ℕ) (κ : Kappa) (noise : CanonicalNoise) (Cg : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
    (C : RenormalisationConstants) (x y : ParabolicSpace) (τ : Symbol)
    (hτ : τ = .noise ∨ τ = .psi ∨ τ = .psiSq ∨ τ = .psiCube) :
    realGermP (canonicalRenormalisedModel N κ noise Cg q hg C) (annKernel0C N) x τ y =
      (hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi C x
        (integration (basis τ)) y := by
  rw [renormalisedExtension_integration_shell_sum_sources N κ noise C x y τ hτ]
  unfold realGermP
  apply tsum_congr
  intro n
  exact canonicalRenormalisedModel_pairing_basis N κ noise Cg q hg C x τ
    (continuous_taylorKernel_right (contDiff_annKernel0C N) n _ x y)
    (hasCompactSupport_taylorKernel (contDiff_annKernel0C N)
      (fun _ hz => annKernel0C_eq_zero N hz) n _ x y)

/-- Actual causal admissibility, derived from Taylor shell pairings. -/
theorem canonicalRenormalisedModel_isRealising (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (Cg : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
    (C : RenormalisationConstants) :
    (canonicalRenormalisedModel N κ noise Cg q hg C).IsRealisingP (annKernel0C N)
      (gamma κ) (phi43PolynomialSector κ) phi43AbstractIntegration phi43IntegrationSector := by
  refine ⟨?_, poly_compatible N κ noise Cg q hg C⟩
  intro x τ _ hV t ht z
  have hτ : τ = .noise ∨ τ = .psi ∨ τ = .psiSq ∨ τ = .psiCube := by
    by_contra hn
    push Not at hn
    have hzero := hV τ hn.1 hn.2.1 hn.2.2.1 hn.2.2.2
    simp at hzero
  rw [canonicalRenormalisedModel_regPi N κ noise Cg q hg C x _ ht]
  have hI : phi43CoordinateEquiv.symm (phi43AbstractIntegration (Pi.single τ 1)) =
      integration (basis τ) := by
    rw [phi43AbstractIntegration_apply, LinearEquiv.symm_apply_apply, coord_symm_single]
  rw [hI, realRegP_of_pos _ _ _ _ ht]
  congr 1
  funext y
  exact (realGerm_sources N κ noise Cg q hg C x y τ hτ).symm

end RegularityStructures.Phi43

end
