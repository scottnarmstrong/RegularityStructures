/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.RenormalisedDerivativeGrowth
public import Phi43.Structure.RenormalisedGlobalModelEnvelopes
public import Phi43.Structure.RenormalisedExtensionJoint
public import Phi43.Structure.CanonicalLocalDerivativeEnvelope
import RegularityStructures.Abstract.Integration.Theorem512.Helpers

/-!
# Polynomially weighted cancellation for the corrected positive sector

The corrected function-valued lift vanishes at the base point on every
positive retained symbol.  Its finite global expansion and derivative growth
therefore give the weighted local increment and whole-space tail estimates
used in [Hai14, Proposition 8.27].
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

private theorem degree_le_one_renormalised (κ : Kappa) (τ : Symbol)
    (hτ : homogeneity κ τ < gamma κ) : homogeneity κ τ ≤ 1 := by
  have hκ0 := κ.property.1
  have hκ1 := κ.property.2
  cases τ <;> simp only [homogeneity, gamma] at hτ ⊢ <;> linarith

theorem renormalisedExtensionPi_positive_increment_envelope (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (Cg : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
    (C : RenormalisationConstants) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ r : ℕ, ∀ τ : Symbol, 0 < homogeneity κ τ → ∀ x y,
      parabolicNorm (y - x) ≤ 1 →
      |(hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi C x
          (basis τ) y| ≤
        B * (1 + parabolicNorm x) ^ r * parabolicNorm (y - x) := by
  let D := hairerCanonicalData (κ := κ) N noise
  obtain ⟨A, hA0, a, hA⟩ := canonicalPolyBounded_finite_envelope
    (fun q' : Symbol × Symbol => fun z => structureGroupMap
      (D.renormalisedExtensionCharacter C z) (basis q'.1) q'.2)
    (fun q' => renormalisedExtensionStructureGroup_coeff_growth N κ noise Cg q hg C q'.1 q'.2)
  obtain ⟨B, hB0, b, hB⟩ := canonicalPolyBounded_finite_envelope
    (fun σ : Symbol => fun z => ‖fderiv ℝ
      (D.renormalisedExtensionGlobalBasis C σ) z‖)
    (fun σ => renormalisedExtensionGlobalBasis_derivative_growth N κ noise Cg q hg C σ)
  refine ⟨(Fintype.card Symbol : ℝ) * A * B * 5 ^ b,
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hA0) hB0) (by positivity),
    a + b, ?_⟩
  intro τ hτ x y hxy
  have he : D.renormalisedExtensionPi C x (basis τ) y =
      ∑ σ : Symbol, structureGroupMap (D.renormalisedExtensionCharacter C x)
        (basis τ) σ * (D.renormalisedExtensionGlobalBasis C σ y -
          D.renormalisedExtensionGlobalBasis C σ x) := by
    calc
      _ = D.renormalisedExtensionPi C x (basis τ) y -
          D.renormalisedExtensionPi C x (basis τ) x := by
        rw [renormalisedExtensionPi_positive_at_base N κ noise C τ hτ x, sub_zero]
      _ = _ := by
        rw [CanonicalData.renormalisedExtensionPi_eq_global_sum,
          CanonicalData.renormalisedExtensionPi_eq_global_sum]
        simp only [D, mul_sub, Finset.sum_sub_distrib]
  rw [he]
  have hinc (σ : Symbol) :
      |D.renormalisedExtensionGlobalBasis C σ y -
          D.renormalisedExtensionGlobalBasis C σ x| ≤
        B * 5 ^ b * (1 + parabolicNorm x) ^ b * parabolicNorm (y - x) := by
    apply canonicalSmooth_local_increment_of_derivative_bound
      (renormalisedExtensionGlobalBasis_smooth N κ noise C σ) B b _ x y hxy
    intro z
    simpa only [abs_of_nonneg (norm_nonneg _)] using hB σ z
  have hterm (σ : Symbol) :
      |structureGroupMap (D.renormalisedExtensionCharacter C x) (basis τ) σ *
        (D.renormalisedExtensionGlobalBasis C σ y -
          D.renormalisedExtensionGlobalBasis C σ x)| ≤
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

theorem renormalisedExtensionPi_positive_weighted_two_power_bound (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (Cg : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
    (C : RenormalisationConstants) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∃ r n : ℕ, 1 ≤ n ∧
      ∀ τ : Symbol, 0 < homogeneity κ τ → homogeneity κ τ < gamma κ → ∀ x y,
        |(hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi C x
            (basis τ) y| ≤
          (1 + parabolicNorm x) ^ r *
            (A * parabolicNorm (y - x) ^ homogeneity κ τ +
              B * parabolicNorm (y - x) ^ (n : ℝ)) := by
  obtain ⟨A, hA0, q', hA⟩ := renormalisedExtensionPi_positive_increment_envelope
    N κ noise Cg q hg C
  obtain ⟨D, hD0, a, b, hD⟩ :=
    renormalisedExtensionPi_global_polynomial_envelope N κ noise Cg q hg C
  let r := max q' (a + b)
  have hB0 : 0 ≤ D * 2 ^ b := mul_nonneg hD0 (by positivity)
  refine ⟨A, D * 2 ^ b, hA0, hB0, r, b + 1, by omega, ?_⟩
  intro τ hτ0 hτγ x y
  have hx1 : 1 ≤ 1 + parabolicNorm x := by linarith [parabolicNorm_nonneg x]
  have hX0 : 0 ≤ (1 + parabolicNorm x) ^ r :=
    pow_nonneg (zero_le_one.trans hx1) _
  have hq : (1 + parabolicNorm x) ^ q' ≤ (1 + parabolicNorm x) ^ r :=
    pow_le_pow_right₀ hx1 (le_max_left _ _)
  have hab : (1 + parabolicNorm x) ^ (a + b) ≤
      (1 + parabolicNorm x) ^ r :=
    pow_le_pow_right₀ hx1 (le_max_right _ _)
  have hd0 := parabolicNorm_nonneg (y - x)
  by_cases hd : parabolicNorm (y - x) ≤ 1
  · have hp : parabolicNorm (y - x) ≤ parabolicNorm (y - x) ^ homogeneity κ τ := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_ge' hd0 hd hτ0.le
          (degree_le_one_renormalised κ τ hτγ)
    calc
      _ ≤ A * (1 + parabolicNorm x) ^ q' * parabolicNorm (y - x) :=
        hA τ hτ0 x y hd
      _ ≤ A * (1 + parabolicNorm x) ^ r * parabolicNorm (y - x) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq hA0) hd0
      _ ≤ A * (1 + parabolicNorm x) ^ r *
          parabolicNorm (y - x) ^ homogeneity κ τ :=
        mul_le_mul_of_nonneg_left hp (mul_nonneg hA0 hX0)
      _ ≤ _ := by
        rw [show A * (1 + parabolicNorm x) ^ r *
          parabolicNorm (y - x) ^ homogeneity κ τ =
            (1 + parabolicNorm x) ^ r *
              (A * parabolicNorm (y - x) ^ homogeneity κ τ) by ring]
        rw [mul_add]
        have hn0 := mul_nonneg hX0
          (mul_nonneg hB0 (Real.rpow_nonneg hd0 (b + 1 : ℕ)))
        exact le_add_of_nonneg_right hn0
  · have hd1 : 1 ≤ parabolicNorm (y - x) := (lt_of_not_ge hd).le
    have hy : (1 + parabolicNorm y) ^ b ≤
        (1 + parabolicNorm x) ^ b *
          (1 + parabolicNorm (y - x)) ^ b := by
      simpa only [mul_pow] using pow_le_pow_left₀
        (by linarith [parabolicNorm_nonneg y]) (one_add_parabolicNorm_le y x) b
    have hb : (1 + parabolicNorm (y - x)) ^ b ≤
        2 ^ b * parabolicNorm (y - x) ^ b := by
      have hh : 1 + parabolicNorm (y - x) ≤ 2 * parabolicNorm (y - x) := by
        linarith
      simpa only [mul_pow] using pow_le_pow_left₀
        (by linarith : 0 ≤ 1 + parabolicNorm (y - x)) hh b
    have hpow : parabolicNorm (y - x) ^ b ≤
        parabolicNorm (y - x) ^ (b + 1) :=
      pow_le_pow_right₀ hd1 (Nat.le_succ _)
    have hfar :
        |(hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi C x
            (basis τ) y| ≤
          (1 + parabolicNorm x) ^ r *
            (D * 2 ^ b * parabolicNorm (y - x) ^ (b + 1)) := by
      calc
        _ ≤ D * (1 + parabolicNorm x) ^ a *
            (1 + parabolicNorm y) ^ b := hD τ x y
        _ ≤ D * (1 + parabolicNorm x) ^ a *
            ((1 + parabolicNorm x) ^ b *
              (1 + parabolicNorm (y - x)) ^ b) :=
          mul_le_mul_of_nonneg_left hy
            (mul_nonneg hD0 (pow_nonneg (zero_le_one.trans hx1) _))
        _ = D * (1 + parabolicNorm x) ^ (a + b) *
            (1 + parabolicNorm (y - x)) ^ b := by
          rw [pow_add]
          ring
        _ ≤ D * (1 + parabolicNorm x) ^ r *
            (2 ^ b * parabolicNorm (y - x) ^ b) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hab hD0) hb
            (pow_nonneg (by linarith) _)
            (mul_nonneg hD0 hX0)
        _ = (1 + parabolicNorm x) ^ r *
            (D * 2 ^ b * parabolicNorm (y - x) ^ b) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpow hB0) hX0
    rw [Real.rpow_natCast]
    exact hfar.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (mul_nonneg hA0 (Real.rpow_nonneg hd0 _))) hX0)

end RegularityStructures.Phi43

end
