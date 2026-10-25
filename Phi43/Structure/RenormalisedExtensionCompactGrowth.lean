/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.RenormalisedExtensionContinuity
public import Phi43.Structure.RenormalisedExtensionFunctions
public import Phi43.Structure.RenormalisedExtensionAlgebra

/-!
# Uniform polynomial tails for compact families of corrected renormalised functions

Hairer [Hai14, Proposition 8.27] in the polynomially weighted framework
of Hoshino [Hos25, Definition 2.1]. The base point ranges over a compact
set; the evaluation point is unrestricted. Bounds are derived from the
finite character expansion and the proved growth of the global trees.
-/

public noncomputable section

namespace RegularityStructures.Phi43

/-- Compact base-point families have a common polynomial envelope. -/
theorem renormalisedExtensionPi_compact_growth (N : ℕ) (κ : Kappa) (noise : CanonicalNoise)
    (hf : PolyBounded noise.zeta) (C : RenormalisationConstants) (τ : Symbol)
    {S : Set ParabolicSpace} (hS : IsCompact S) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ p : ℕ, ∀ x ∈ S, ∀ y,
      |(hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi C x (basis τ) y| ≤
        B * (1 + parabolicNorm y) ^ p := by
  let D := hairerCanonicalData (κ := κ) N noise
  have hg (σ : Symbol) := (renormalisedExtensionGlobalBasis_growth N κ noise hf C σ).2
  choose B p hp using hg
  have hB0 (σ : Symbol) : 0 ≤ B σ := nonneg_of_bound (hp σ)
  have hc (σ : Symbol) : ∃ A : ℝ, ∀ x ∈ S,
      |structureGroupMap (D.renormalisedExtensionCharacter C x) (basis τ) σ| ≤ A := by
    obtain ⟨A, hA⟩ := hS.exists_bound_of_continuousOn
      (continuous_renormalisedExtensionStructureGroup_coeff N noise C τ σ).continuousOn
    exact ⟨A, fun x hx => by simpa only [Real.norm_eq_abs] using hA x hx⟩
  choose A hA using hc
  let q := ∑ σ : Symbol, p σ
  have hpq (σ : Symbol) : p σ ≤ q :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ σ)
  refine ⟨∑ σ : Symbol, max (A σ) 0 * B σ,
    Finset.sum_nonneg (fun σ _ => mul_nonneg (le_max_right _ _) (hB0 σ)), q, ?_⟩
  intro x hx y
  have he : D.renormalisedExtensionPi C x (basis τ) y =
      ∑ σ : Symbol, structureGroupMap (D.renormalisedExtensionCharacter C x) (basis τ) σ *
        D.renormalisedExtensionGlobalBasis C σ y := by
    exact D.renormalisedExtensionPi_eq_global_sum C x y (basis τ)
  rw [he, Finset.sum_mul]
  have hs : |∑ σ : Symbol, structureGroupMap (D.renormalisedExtensionCharacter C x) (basis τ) σ *
      D.renormalisedExtensionGlobalBasis C σ y| ≤ ∑ σ : Symbol,
      |structureGroupMap (D.renormalisedExtensionCharacter C x) (basis τ) σ * D.renormalisedExtensionGlobalBasis C σ y| := by
    simpa only [Real.norm_eq_abs] using norm_sum_le Finset.univ
      (fun σ => structureGroupMap (D.renormalisedExtensionCharacter C x) (basis τ) σ * D.renormalisedExtensionGlobalBasis C σ y)
  refine hs.trans (Finset.sum_le_sum fun σ _ => ?_)
  rw [abs_mul]
  have hpow : (1 + parabolicNorm y) ^ p σ ≤ (1 + parabolicNorm y) ^ q :=
    pow_le_pow_right₀ (by linarith [parabolicNorm_nonneg y]) (hpq σ)
  calc
    _ ≤ max (A σ) 0 * (B σ * (1 + parabolicNorm y) ^ p σ) :=
      mul_le_mul ((hA σ x hx).trans (le_max_left _ _)) (hp σ y)
        (abs_nonneg _) (le_max_right _ _)
    _ ≤ max (A σ) 0 * (B σ * (1 + parabolicNorm y) ^ q) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (hB0 σ))
        (le_max_right _ _)
    _ = _ := by ring

end RegularityStructures.Phi43

end

