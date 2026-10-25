/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.RenormalisedCharacterGrowth
public import Phi43.Structure.RenormalisedExtensionFunctions
public import Phi43.Structure.RenormalisedExtensionAlgebra
public import Phi43.Structure.CanonicalFiniteEnvelopes
import RegularityStructures.Abstract.Integration.Theorem512.Helpers

/-!
# Global polynomial envelopes for the corrected smooth lift

The finite corrected character expansion and the explicit renormalised global
trees give simultaneous polynomial growth in the base and evaluation points.
This is the weighted analogue of [Hai14, Proposition 8.27] and uses no model
bound as an input.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

theorem renormalisedExtensionPi_global_polynomial_envelope (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (Cg : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
    (C : RenormalisationConstants) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ a b : ℕ, ∀ τ : Symbol, ∀ x y,
      |(hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi C x
          (basis τ) y| ≤
        B * (1 + parabolicNorm x) ^ a * (1 + parabolicNorm y) ^ b := by
  let D := hairerCanonicalData (κ := κ) N noise
  let hf := canonicalNoise_polyBounded_of_derivatives noise Cg q hg
  obtain ⟨A, hA0, a, hA⟩ := canonicalPolyBounded_finite_envelope
    (fun q' : Symbol × Symbol => fun z => structureGroupMap
      (D.renormalisedExtensionCharacter C z) (basis q'.1) q'.2)
    (fun q' => renormalisedExtensionStructureGroup_coeff_growth N κ noise Cg q hg C q'.1 q'.2)
  obtain ⟨B, hB0, b, hB⟩ := canonicalPolyBounded_finite_envelope
    (D.renormalisedExtensionGlobalBasis C)
    (fun τ => renormalisedExtensionGlobalBasis_growth N κ noise hf C τ)
  refine ⟨(Fintype.card Symbol : ℝ) * A * B,
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hA0) hB0, a, b, ?_⟩
  intro τ x y
  rw [CanonicalData.renormalisedExtensionPi_eq_global_sum D C x y (basis τ)]
  have hterm (σ : Symbol) :
      |structureGroupMap (D.renormalisedExtensionCharacter C x) (basis τ) σ *
          D.renormalisedExtensionGlobalBasis C σ y| ≤
        (A * (1 + parabolicNorm x) ^ a) *
          (B * (1 + parabolicNorm y) ^ b) := by
    rw [abs_mul]
    exact mul_le_mul (hA (τ, σ) x) (hB σ y) (abs_nonneg _)
      (mul_nonneg hA0 (pow_nonneg (by linarith [parabolicNorm_nonneg x]) _))
  have hs := (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (s := Finset.univ) (fun σ _ => hterm σ))
  refine hs.trans_eq ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

end RegularityStructures.Phi43

end
