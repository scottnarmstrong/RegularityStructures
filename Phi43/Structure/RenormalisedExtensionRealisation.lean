/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.RenormalisedExtensionFunctions
public import Phi43.Structure.RenormalisedExtensionAlgebra
public import Phi43.Structure.CanonicalSmoothRealisation
public import RegularityStructures.Abstract.Integration.Commute.Reg

/-!+# Distributional realisation of the explicit renormalised extension

The distributions below regularise the explicit corrected tree functions;
no arbitrary covariant pi field is supplied. These are construction lemmas
for Hairer [Hai14, Theorem 8.44]. Identification with the tensor action on
H0 and admissibility are separate obligations.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

open scoped ContDiff in
theorem renormalisedExtensionPi_smooth (N : ℕ) {κ : Kappa} (noise : CanonicalNoise)
    (c : RenormalisationConstants) (x : ParabolicSpace) (v : T) :
    ContDiff ℝ ∞ ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi c x v) := by
  have he := funext fun y => CanonicalData.renormalisedExtensionPi_eq_global_sum
    (hairerCanonicalData (κ := κ) N noise) c x y v
  rw [he]
  exact ContDiff.sum fun τ _ =>
    contDiff_const.mul (renormalisedExtensionGlobalBasis_smooth N κ noise c τ)

theorem renormalisedExtensionPi_growth (N : ℕ) {κ : Kappa} (noise : CanonicalNoise)
    (hf : PolyBounded noise.zeta) (c : RenormalisationConstants) (x : ParabolicSpace) (v : T) :
    PolyBounded ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi c x v) := by
  have he := funext fun y => CanonicalData.renormalisedExtensionPi_eq_global_sum
    (hairerCanonicalData (κ := κ) N noise) c x y v
  rw [he]
  exact PolyBounded.finsetSum Finset.univ _ _
    (fun τ _ => renormalisedExtensionGlobalBasis_growth N κ noise hf c τ)

/-- Q-regularisation of the explicitly defined renormalised functions. -/
def renormalisedExtensionDistribution (N : ℕ) {κ : Kappa} (noise : CanonicalNoise)
    (hf : PolyBounded noise.zeta) (c : RenormalisationConstants) (x : ParabolicSpace) (v : T) :
    parabolicSemigroup.distributions :=
  canonicalSmoothReg ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi c x v)
    (renormalisedExtensionPi_growth N noise hf c x v)

theorem renormalisedExtensionDistribution_covariance (N : ℕ) {κ : Kappa}
    (noise : CanonicalNoise) (hf : PolyBounded noise.zeta) (c : RenormalisationConstants)
    (x y : ParabolicSpace) (v : T) :
    renormalisedExtensionDistribution N (κ := κ) noise hf c x
      ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGamma c x y v) =
        renormalisedExtensionDistribution N (κ := κ) noise hf c y v := by
  apply Subtype.ext
  funext t z
  change (if 0 < t then parabolicSemigroup.apply t
    ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi c x
      ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGamma c x y v)) z else 0) = _
  rw [CanonicalData.renormalisedExtensionPi_gamma]
  rfl

/-- Linearity follows from the actual Q convolution, not from a certificate. -/
def renormalisedExtensionDistributionLinear (N : ℕ) {κ : Kappa} (noise : CanonicalNoise)
    (hf : PolyBounded noise.zeta) (c : RenormalisationConstants) (x : ParabolicSpace) :
    T →ₗ[ℝ] parabolicSemigroup.distributions where
  toFun := renormalisedExtensionDistribution N (κ := κ) noise hf c x
  map_add' v w := by
    apply Subtype.ext
    funext t z
    by_cases ht : 0 < t
    · simp only [Submodule.coe_add, Pi.add_apply, renormalisedExtensionDistribution,
        canonicalSmoothReg, ht, ite_true]
      change parabolicSemigroup.apply t
        ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi c x (v + w)) z = _
      rw [map_add]
      exact PolyBounded.apply_add (renormalisedExtensionPi_growth N noise hf c x v)
        (renormalisedExtensionPi_growth N noise hf c x w) ht z
    · simp [renormalisedExtensionDistribution, canonicalSmoothReg, ht]
  map_smul' r v := by
    apply Subtype.ext
    funext t z
    by_cases ht : 0 < t
    · simp only [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply,
        renormalisedExtensionDistribution, canonicalSmoothReg, ht, ite_true]
      change parabolicSemigroup.apply t
        ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi c x (r • v)) z = _
      rw [map_smul]
      simp only [RegularisingSemigroup.apply, Pi.smul_apply, smul_eq_mul,
        mul_left_comm _ r]
      rw [integral_const_mul]
    · simp [renormalisedExtensionDistribution, canonicalSmoothReg, ht]

theorem renormalisedExtensionDistribution_reg_eq_sum (N : ℕ) {κ : Kappa}
    (noise : CanonicalNoise) (hf : PolyBounded noise.zeta) (c : RenormalisationConstants)
    (x : ParabolicSpace) (v : T) {t : ℝ} (ht : 0 < t) (z : ParabolicSpace) :
    (renormalisedExtensionDistribution N (κ := κ) noise hf c x v :
      ℝ → ParabolicSpace → ℝ) t z =
      ∑ τ : Symbol,
        structureGroupMap ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionCharacter c x)
          v τ * parabolicSemigroup.apply t
            ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGlobalBasis c τ) z := by
  change (if 0 < t then parabolicSemigroup.apply t
    ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi c x v) z else 0) = _
  rw [ite_eq_left ht]
  have he := funext fun y => CanonicalData.renormalisedExtensionPi_eq_global_sum
    (hairerCanonicalData (κ := κ) N noise) c x y v
  rw [he]
  exact PolyBounded.apply_finsetSum Finset.univ _ _
    (fun τ _ => renormalisedExtensionGlobalBasis_growth N κ noise hf c τ) ht z

end RegularityStructures.Phi43

end
