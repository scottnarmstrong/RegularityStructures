/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.PositiveMomentGammaOne
public import Phi43.Structure.CanonicalCoreUniqueness
public import Phi43.Structure.CanonicalModelExistence
public import Phi43.Structure.RenormalisedExtensionTensorIntegration
public import RegularityStructures.Abstract.Integration.Theorem512.Helpers

/-!
# `Q_t Π_x` on the integrated sources is determined by the canonical model predicate

For `Z` satisfying `IsRenormalisedCanonicalModel N κ noise C Z` and a noise with polynomially
bounded derivatives (up to order `4`), the regularised realisation of `Z` on the integrated sources
`I(Ψ²) = I Ψ²` and `I(Ψ³)` is that of the explicit corrected extension model
(`regPi_integrated_source_eq_extension`): `Z` and the explicit model both realise the kernel, and
their `F₋` realisations agree (`canonicalModels_pi_integrated_source_eq`).

Consequently the `1`-entry of `Γ_{yx} e_τ` is the constant `P` whenever the explicit extension
functions satisfy `Π̂_x e_τ - Π̂_y e_τ ≡ P` (`gammaMap_one_entry_eq_of_extension_sub`).
-/

public section

namespace RegularityStructures.Phi43

open RegularityStructures

variable {N : ℕ} {κ : Kappa} {noise : CanonicalNoise} {C : RenormalisationConstants}
  {Z : Model (phi43RegularityStructure κ) parabolicSemigroup}

private theorem integration_single_eq (τ : Symbol)
    (hτ : τ = Symbol.psiSq ∨ τ = Symbol.psiCube) (σ : Symbol)
    (hσ : (τ = Symbol.psiSq ∧ σ = Symbol.iPsiSq) ∨ (τ = Symbol.psiCube ∧ σ = Symbol.iPsiCube)) :
    phi43AbstractIntegration (Pi.single τ (1 : ℝ) : Symbol → ℝ) = Pi.single σ 1 := by
  funext j
  rw [phi43AbstractIntegration_apply_coord]
  rcases hσ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases j <;> simp

private theorem coordinateEquiv_symm_single (σ : Symbol) :
    phi43CoordinateEquiv.symm (Pi.single σ (1 : ℝ) : Symbol → ℝ) = basis σ := by
  apply phi43CoordinateEquiv.injective
  simp [phi43CoordinateEquiv_basis]

/-- **Identification of `Q_t Π_x` on the integrated sources** with the explicit extension. -/
theorem regPi_integrated_source_eq_extension (Cg : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
    (hZ : Statements.IsRenormalisedCanonicalModel N κ noise C Z) (τ σ : Symbol)
    (hτ : τ = Symbol.psiSq ∨ τ = Symbol.psiCube)
    (hσ : (τ = Symbol.psiSq ∧ σ = Symbol.iPsiSq) ∨ (τ = Symbol.psiCube ∧ σ = Symbol.iPsiCube))
    (x : ParabolicSpace) {t : ℝ} (ht : 0 < t) (z : ParabolicSpace) :
    Z.regPi x (Pi.single σ (1 : ℝ) : Symbol → ℝ) t z =
      parabolicSemigroup.apply t
        ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi C x (basis σ)) z := by
  have hZ' := canonicalRenormalisedModel_isRenormalisedCanonicalModel N κ noise Cg q hg C
  have hτ' : τ = Symbol.noise ∨ τ = Symbol.psi ∨ τ = Symbol.psiSq ∨ τ = Symbol.psiCube := by
    tauto
  have h := canonicalModels_pi_integrated_source_eq N κ noise C Z _ hZ hZ' τ hτ' x
  rw [integration_single_eq τ hτ σ hσ] at h
  have h2 : Z.regPi x (Pi.single σ (1 : ℝ) : Symbol → ℝ) t z =
      (canonicalRenormalisedModel N κ noise Cg q hg C).regPi x
        (Pi.single σ (1 : ℝ) : Symbol → ℝ) t z := by
    change ((Z.pi x (Pi.single σ (1 : ℝ) : Symbol → ℝ) : ℝ → ParabolicSpace → ℝ) t z) = _
    rw [h]; rfl
  rw [h2, canonicalRenormalisedModel_regPi N κ noise Cg q hg C x _ ht, coordinateEquiv_symm_single]

/-- **The `1`-entry of `Γ_{yx} e_σ` is the constant `P`** when the explicit extension functions
satisfy `Π̂_x e_σ - Π̂_y e_σ ≡ P`, for `σ = I(Ψ²), I(Ψ³)`. -/
theorem gammaMap_one_entry_eq_of_extension_sub (Cg : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
    (hZ : Statements.IsRenormalisedCanonicalModel N κ noise C Z) (τ σ : Symbol)
    (hτ : τ = Symbol.psiSq ∨ τ = Symbol.psiCube)
    (hσ : (τ = Symbol.psiSq ∧ σ = Symbol.iPsiSq) ∨ (τ = Symbol.psiCube ∧ σ = Symbol.iPsiCube))
    (hentry : ∀ y x : ParabolicSpace, Z.gammaMap y x (Pi.single σ (1 : ℝ) : Symbol → ℝ) =
      (Pi.single σ (1 : ℝ) : Symbol → ℝ) +
        Z.gammaMap y x (Pi.single σ (1 : ℝ) : Symbol → ℝ) Symbol.one •
          (Pi.single Symbol.one (1 : ℝ) : Symbol → ℝ))
    (y x : ParabolicSpace) (P : ℝ)
    (hP : ∀ w, (hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi C x (basis σ) w -
      (hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi C y (basis σ) w = P) :
    Z.gammaMap y x (Pi.single σ (1 : ℝ) : Symbol → ℝ) Symbol.one = P := by
  have hf := canonicalNoise_polyBounded_of_derivatives noise Cg q hg
  have hpoly := hZ.1.poly
  have ht : (0 : ℝ) < 1 := one_pos
  rw [gammaMap_one_entry_eq_sub hpoly y x σ (hentry y x) ht (0 : ParabolicSpace),
    regPi_integrated_source_eq_extension Cg q hg hZ τ σ hτ hσ x ht,
    regPi_integrated_source_eq_extension Cg q hg hZ τ σ hτ hσ y ht,
    ← PolyBounded.apply_sub (renormalisedExtensionPi_growth N noise hf C x _)
      (renormalisedExtensionPi_growth N noise hf C y _) ht]
  simp_rw [hP]
  simp only [RegularisingSemigroup.apply]
  rw [MeasureTheory.integral_mul_const, parabolicSemigroup_isConservative ht, one_mul]

end RegularityStructures.Phi43

end
