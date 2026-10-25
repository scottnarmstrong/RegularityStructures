/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalFiniteEnvelopes
public import Phi43.Structure.CanonicalLocalDerivativeEnvelope
public import Phi43.Structure.CanonicalSmoothCancellation
public import Phi43.Structure.CanonicalSmoothBasis

/-!
# Global polynomial envelopes for the canonical function family

Hairer [Hai14, Proposition 8.27] in the weighted framework
[Hos25, Definition 2.1]. All constants below are derived from the
actual finite character expansion and global-tree derivative bounds.
-/

public noncomputable section

namespace RegularityStructures.Phi43

/-- Polynomial growth simultaneously in the base and evaluation points. -/
theorem canonicalPi_global_polynomial_envelope (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (C : ℝ) (p : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ C * (1 + parabolicNorm z) ^ p) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ a b : ℕ, ∀ τ : Symbol, ∀ x y,
      |(hairerCanonicalData (κ := κ) N noise).canonicalPi x (basis τ) y| ≤
        B * (1 + parabolicNorm x) ^ a * (1 + parabolicNorm y) ^ b := by
  let D := hairerCanonicalData (κ := κ) N noise
  obtain ⟨A, hA0, a, hA⟩ := canonicalPolyBounded_finite_envelope
    (fun q : Symbol × Symbol => fun z => structureGroupMap (D.canonicalCharacter z) (basis q.1) q.2)
    (fun q => canonicalStructureGroup_coeff_growth N κ noise C p hg q.1 q.2)
  obtain ⟨B, hB0, b, hB⟩ := canonicalPolyBounded_finite_envelope D.globalPiBasis
    (canonicalGlobalPiBasis_growth N noise (canonicalNoise_polyBounded_of_derivatives noise C p hg))
  refine ⟨(Fintype.card Symbol : ℝ) * A * B,
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hA0) hB0, a, b, ?_⟩
  intro τ x y
  rw [canonicalPi_eq_global_sum]
  have hterm (σ : Symbol) :
      |structureGroupMap (D.canonicalCharacter x) (basis τ) σ * D.globalPiBasis σ y| ≤
        (A * (1 + parabolicNorm x) ^ a) * (B * (1 + parabolicNorm y) ^ b) := by
    rw [abs_mul]
    exact mul_le_mul (hA (τ, σ) x) (hB σ y) (abs_nonneg _)
      (mul_nonneg hA0 (pow_nonneg (by linarith [parabolicNorm_nonneg x]) _))
  have hs := (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (s := Finset.univ) (fun σ _ => hterm σ))
  refine hs.trans_eq ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- The positive canonical sector has a local cancellation bound whose
constant grows polynomially in its unrestricted base point. -/
theorem canonicalPi_positive_increment_envelope (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (C : ℝ) (p : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ C * (1 + parabolicNorm z) ^ p) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ q : ℕ, ∀ τ : Symbol, 0 < homogeneity κ τ → ∀ x y,
      parabolicNorm (y - x) ≤ 1 →
      |(hairerCanonicalData (κ := κ) N noise).canonicalPi x (basis τ) y| ≤
        B * (1 + parabolicNorm x) ^ q * parabolicNorm (y - x) := by
  let D := hairerCanonicalData (κ := κ) N noise
  obtain ⟨A, hA0, a, hA⟩ := canonicalPolyBounded_finite_envelope
    (fun q : Symbol × Symbol => fun z => structureGroupMap (D.canonicalCharacter z) (basis q.1) q.2)
    (fun q => canonicalStructureGroup_coeff_growth N κ noise C p hg q.1 q.2)
  obtain ⟨B, hB0, b, hB⟩ := canonicalPolyBounded_finite_envelope
    (fun σ : Symbol => fun z => ‖fderiv ℝ (D.globalPiBasis σ) z‖)
    (canonicalGlobalPiBasis_derivative_growth N κ noise C p hg)
  refine ⟨(Fintype.card Symbol : ℝ) * A * B * 5 ^ b,
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hA0) hB0) (by positivity), a + b, ?_⟩
  intro τ hτ x y hxy
  have he : D.canonicalPi x (basis τ) y =
      ∑ σ : Symbol, structureGroupMap (D.canonicalCharacter x) (basis τ) σ *
        (D.globalPiBasis σ y - D.globalPiBasis σ x) := by
    calc
      _ = D.canonicalPi x (basis τ) y - D.canonicalPi x (basis τ) x := by
        rw [canonicalPi_positive_at_base N κ noise τ hτ x, sub_zero]
      _ = _ := by
        rw [canonicalPi_eq_global_sum, canonicalPi_eq_global_sum]
        simp only [D, mul_sub, Finset.sum_sub_distrib]
  rw [he]
  have hinc (σ : Symbol) : |D.globalPiBasis σ y - D.globalPiBasis σ x| ≤
      B * 5 ^ b * (1 + parabolicNorm x) ^ b * parabolicNorm (y - x) := by
    apply canonicalSmooth_local_increment_of_derivative_bound
      (canonicalGlobalPiBasis_smooth N noise σ) B b _ x y hxy
    intro z
    simpa only [abs_of_nonneg (norm_nonneg _)] using hB σ z
  have hterm (σ : Symbol) :
      |structureGroupMap (D.canonicalCharacter x) (basis τ) σ *
        (D.globalPiBasis σ y - D.globalPiBasis σ x)| ≤
        (A * (1 + parabolicNorm x) ^ a) *
          (B * 5 ^ b * (1 + parabolicNorm x) ^ b * parabolicNorm (y - x)) := by
    rw [abs_mul]
    exact mul_le_mul (hA (τ, σ) x) (hinc σ) (abs_nonneg _)
      (mul_nonneg hA0 (pow_nonneg (by linarith [parabolicNorm_nonneg x]) _))
  have hs := (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (s := Finset.univ) (fun σ _ => hterm σ))
  refine hs.trans_eq ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, pow_add]
  ring

end RegularityStructures.Phi43

end
