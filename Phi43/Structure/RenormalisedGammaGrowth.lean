/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.EnlargedCanonicalModel
public import Phi43.Structure.RenormalisedExtensionAdmissible
public import Phi43.Structure.RenormalisedGammaLocal
public import Phi43.Structure.RenormalisedPositivePolynomialTails
public import Phi43.Structure.RenormalisedGlobalModelEnvelopes
public import Phi43.Structure.CanonicalGlobalModelEnvelopes
public import Phi43.Structure.CanonicalGammaGrowthComponents
public import Phi43.Structure.CanonicalSecondDerivativeGrowth
public import Phi43.Structure.CanonicalGammaActionBounds
public import Phi43.Structure.CanonicalCharacterGrowth
public import RegularityStructures.Abstract.Integration.Growth.Setting
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
public import RegularityStructures.Probability.ModelKolmogorovQFamilyWeightedSemigroup

/-!
# Whole-space weighted Gamma growth for the corrected finite character

The corrected character has the same shift, `J(Ψ)`, gradient, and square
primitive coefficients as the canonical character. Its integrated-cubic
coefficient is controlled by the corrected positive-sector increment estimate.
The finite multiplicative action then gives the weighted Gamma bound required
by the planted extension. This is the weighted form of Hairer [Hai14,
Proposition 8.27] and the corrected character identity [Hai14, (9.4c)].
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures.Phi43

private theorem renormalisedGamma_cPsi_eq_canonical (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (C : RenormalisationConstants) (x y : ParabolicSpace) :
    ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGammaParameter C y x).cPsi =
      ((hairerCanonicalData (κ := κ) N noise).canonicalGammaParameter y x).cPsi := by
  simp [CanonicalData.renormalisedExtensionGammaParameter,
    CanonicalData.renormalisedExtensionCharacter,
    CanonicalData.canonicalGammaParameter, structureGroupInv]

private theorem renormalisedGamma_cPsiGrad_eq_canonical (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (C : RenormalisationConstants) (x y : ParabolicSpace)
    (i : Fin 3) :
    ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGammaParameter C y x).cPsiGrad i =
      ((hairerCanonicalData (κ := κ) N noise).canonicalGammaParameter y x).cPsiGrad i := by
  simp [CanonicalData.renormalisedExtensionGammaParameter,
    CanonicalData.renormalisedExtensionCharacter,
    CanonicalData.canonicalGammaParameter, structureGroupInv]

private theorem renormalisedGamma_cPsiSq_eq_canonical (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (C : RenormalisationConstants) (x y : ParabolicSpace) :
    ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGammaParameter C y x).cPsiSq =
      ((hairerCanonicalData (κ := κ) N noise).canonicalGammaParameter y x).cPsiSq := by
  simp [CanonicalData.renormalisedExtensionGammaParameter,
    CanonicalData.renormalisedExtensionCharacter,
    CanonicalData.canonicalGammaParameter, structureGroupInv]

private theorem canonicalGamma_cPsiGrad_eq_character_sub (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (x y : ParabolicSpace) (i : Fin 3) :
    ((hairerCanonicalData (κ := κ) N noise).canonicalGammaParameter y x).cPsiGrad i =
      ((hairerCanonicalData (κ := κ) N noise).canonicalCharacter x).cPsiGrad i -
        ((hairerCanonicalData (κ := κ) N noise).canonicalCharacter y).cPsiGrad i := by
  simp [CanonicalData.canonicalGammaParameter, structureGroupInv]
  ring

private theorem combine_local_global_bound_fixed
    {F : ParabolicSpace → ParabolicSpace → ℝ} {α : ℝ}
    {Bl Bg : ℝ} {rl rg sg : ℕ} (hα : 0 ≤ α) (hBl : 0 ≤ Bl) (hBg : 0 ≤ Bg)
    (hl : ∀ x y, parabolicNorm (y - x) ≤ 1 →
      |F x y| ≤ Bl * (1 + parabolicNorm x) ^ rl *
        parabolicNorm (y - x) ^ α)
    (hg : ∀ x y, |F x y| ≤ Bg * (1 + parabolicNorm x) ^ rg *
      (1 + parabolicNorm y) ^ sg) :
    ∀ x y, |F x y| ≤ (Bl + Bg) * (1 + parabolicNorm x) ^ (rl + rg + sg) *
      (1 + parabolicNorm (y - x)) ^ sg * parabolicNorm (y - x) ^ α := by
  intro x y
  let d := parabolicNorm (y - x)
  have hx1 : 1 ≤ 1 + parabolicNorm x := by
    linarith [parabolicNorm_nonneg x]
  have hX : 0 ≤ (1 + parabolicNorm x) ^ (rl + rg + sg) := by positivity
  have hd0 : 0 ≤ d := by dsimp [d]; exact parabolicNorm_nonneg _
  have hD : 0 ≤ (1 + d) ^ sg := pow_nonneg (by linarith) _
  have hαn : 0 ≤ d ^ α := Real.rpow_nonneg (parabolicNorm_nonneg _) _
  by_cases hsmall : d ≤ 1
  · have hr : (1 + parabolicNorm x) ^ rl ≤
        (1 + parabolicNorm x) ^ (rl + rg + sg) :=
      pow_le_pow_right₀ hx1 (by omega)
    have hs : 1 ≤ (1 + d) ^ sg := one_le_pow₀ (by linarith [parabolicNorm_nonneg (y - x)])
    have h1 : Bl * (1 + parabolicNorm x) ^ rl * d ^ α ≤
        Bl * (1 + parabolicNorm x) ^ (rl + rg + sg) * d ^ α :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hBl) hαn
    have h2 : Bl * (1 + parabolicNorm x) ^ (rl + rg + sg) * d ^ α ≤
        (Bl + Bg) * (1 + parabolicNorm x) ^ (rl + rg + sg) * d ^ α :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hBg) hX) hαn
    have h3 : (Bl + Bg) * (1 + parabolicNorm x) ^ (rl + rg + sg) * d ^ α ≤
        (Bl + Bg) * (1 + parabolicNorm x) ^ (rl + rg + sg) *
          (1 + d) ^ sg * d ^ α := by
      calc
        _ ≤ ((Bl + Bg) * (1 + parabolicNorm x) ^ (rl + rg + sg) * d ^ α) *
              (1 + d) ^ sg := le_mul_of_one_le_right
                (mul_nonneg (mul_nonneg (add_nonneg hBl hBg) hX) hαn) hs
        _ = _ := by ring
    simpa only [d] using (hl x y hsmall).trans (h1.trans (h2.trans h3))
  · have hlarge : 1 ≤ d := le_of_lt (lt_of_not_ge hsmall)
    have hy := one_add_parabolicNorm_le y x
    have hpow : (1 + parabolicNorm y) ^ sg ≤
        ((1 + parabolicNorm x) * (1 + d)) ^ sg := by
      exact pow_le_pow_left₀ (by linarith [parabolicNorm_nonneg y])
        (by simpa [d] using hy) sg
    rw [mul_pow] at hpow
    have h1 : Bg * (1 + parabolicNorm x) ^ rg * (1 + parabolicNorm y) ^ sg ≤
        Bg * (1 + parabolicNorm x) ^ rg *
          ((1 + parabolicNorm x) ^ sg * (1 + d) ^ sg) :=
      mul_le_mul_of_nonneg_left hpow (mul_nonneg hBg (pow_nonneg (by positivity) _))
    have h2 : Bg * (1 + parabolicNorm x) ^ rg *
          ((1 + parabolicNorm x) ^ sg * (1 + d) ^ sg) ≤
        Bg * (1 + parabolicNorm x) ^ (rl + rg + sg) * (1 + d) ^ sg := by
      have hr : (1 + parabolicNorm x) ^ (rg + sg) ≤
          (1 + parabolicNorm x) ^ (rl + rg + sg) :=
        pow_le_pow_right₀ hx1 (by omega)
      calc
        _ = Bg * ((1 + parabolicNorm x) ^ rg *
              (1 + parabolicNorm x) ^ sg) * (1 + d) ^ sg := by ring
        _ = Bg * (1 + parabolicNorm x) ^ (rg + sg) * (1 + d) ^ sg := by
          rw [pow_add]
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hr hBg) hD
    have h3 : Bg * (1 + parabolicNorm x) ^ (rl + rg + sg) * (1 + d) ^ sg ≤
        (Bl + Bg) * (1 + parabolicNorm x) ^ (rl + rg + sg) * (1 + d) ^ sg :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hBl) hX) hD
    have hα1 : 1 ≤ d ^ α := Real.one_le_rpow hlarge hα
    have h4 : (Bl + Bg) * (1 + parabolicNorm x) ^ (rl + rg + sg) *
          (1 + d) ^ sg ≤
        (Bl + Bg) * (1 + parabolicNorm x) ^ (rl + rg + sg) *
          (1 + d) ^ sg * d ^ α :=
      le_mul_of_one_le_right (mul_nonneg (mul_nonneg (add_nonneg hBl hBg) hX) hD) hα1
    simpa only [d] using (hg x y).trans (h1.trans (h2.trans (h3.trans h4)))

private theorem finite_two_point_global_family {ι : Type*} [Fintype ι]
    (f : ι → ParabolicSpace → ℝ) {B : ℝ} {r : ℕ} (hB : 0 ≤ B)
    (hf : ∀ i z, |f i z| ≤ B * (1 + parabolicNorm z) ^ r) :
    ∀ i x y, |f i y - f i x| ≤ 2 * B * (1 + parabolicNorm x) ^ r *
      (1 + parabolicNorm (y - x)) ^ r := by
  intro i x y
  have hpow : (1 + parabolicNorm y) ^ r ≤
      (1 + parabolicNorm x) ^ r * (1 + parabolicNorm (y - x)) ^ r := by
    exact (pow_le_pow_left₀ (by linarith [parabolicNorm_nonneg y])
      (one_add_parabolicNorm_le y x) r).trans_eq (mul_pow _ _ _)
  have hX : 0 ≤ (1 + parabolicNorm x) ^ r :=
    pow_nonneg (by linarith [parabolicNorm_nonneg x]) _
  have hD : 1 ≤ (1 + parabolicNorm (y - x)) ^ r :=
    one_le_pow₀ (by linarith [parabolicNorm_nonneg (y - x)])
  calc
    |f i y - f i x| ≤ |f i y| + |f i x| := abs_sub _ _
    _ ≤ B * (1 + parabolicNorm y) ^ r + B * (1 + parabolicNorm x) ^ r :=
      add_le_add (hf i y) (hf i x)
    _ ≤ B * ((1 + parabolicNorm x) ^ r *
          (1 + parabolicNorm (y - x)) ^ r) + B * (1 + parabolicNorm x) ^ r :=
      add_le_add (mul_le_mul_of_nonneg_left hpow hB) (le_refl _)
    _ ≤ 2 * B * (1 + parabolicNorm x) ^ r *
          (1 + parabolicNorm (y - x)) ^ r := by
      have hmain : B * (1 + parabolicNorm x) ^ r ≤
          B * (1 + parabolicNorm x) ^ r *
            (1 + parabolicNorm (y - x)) ^ r :=
        le_mul_of_one_le_right (mul_nonneg hB hX) hD
      calc
        _ = B * (1 + parabolicNorm x) ^ r *
              (1 + parabolicNorm (y - x)) ^ r +
            B * (1 + parabolicNorm x) ^ r := by ring
        _ ≤ B * (1 + parabolicNorm x) ^ r *
              (1 + parabolicNorm (y - x)) ^ r +
            B * (1 + parabolicNorm x) ^ r *
              (1 + parabolicNorm (y - x)) ^ r := add_le_add_right hmain _
        _ = _ := by ring

private theorem enlarge_weighted_bound
    {F : ParabolicSpace → ParabolicSpace → ℝ} {α : ℝ}
    {B A : ℝ} {r s R S : ℕ} (_hα : 0 ≤ α) (hB : 0 ≤ B)
    (hBA : B ≤ A) (hr : r ≤ R) (hs : s ≤ S) (x y : ParabolicSpace)
    (h : |F x y| ≤ B * (1 + parabolicNorm x) ^ r *
      (1 + parabolicNorm (y - x)) ^ s * parabolicNorm (y - x) ^ α) :
    |F x y| ≤ A * (1 + parabolicNorm x) ^ R *
      (1 + parabolicNorm (y - x)) ^ S * parabolicNorm (y - x) ^ α := by
  have hx : (1 + parabolicNorm x) ^ r ≤ (1 + parabolicNorm x) ^ R :=
    pow_le_pow_right₀ (by linarith [parabolicNorm_nonneg x]) hr
  have hd : (1 + parabolicNorm (y - x)) ^ s ≤
      (1 + parabolicNorm (y - x)) ^ S :=
    pow_le_pow_right₀ (by linarith [parabolicNorm_nonneg (y - x)]) hs
  have hxn : 0 ≤ (1 + parabolicNorm x) ^ R :=
    pow_nonneg (by linarith [parabolicNorm_nonneg x]) _
  have hdn : 0 ≤ (1 + parabolicNorm (y - x)) ^ S :=
    pow_nonneg (by linarith [parabolicNorm_nonneg (y - x)]) _
  have hαn : 0 ≤ parabolicNorm (y - x) ^ α :=
    Real.rpow_nonneg (parabolicNorm_nonneg _) _
  calc
    |F x y| ≤ B * (1 + parabolicNorm x) ^ R *
        (1 + parabolicNorm (y - x)) ^ s * parabolicNorm (y - x) ^ α := by
      exact h.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hx hB)
          (pow_nonneg (by linarith [parabolicNorm_nonneg (y - x)]) _)) hαn)
    _ ≤ B * (1 + parabolicNorm x) ^ R *
        (1 + parabolicNorm (y - x)) ^ S * parabolicNorm (y - x) ^ α := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hd (mul_nonneg hB hxn)) hαn
    _ ≤ A * (1 + parabolicNorm x) ^ R *
        (1 + parabolicNorm (y - x)) ^ S * parabolicNorm (y - x) ^ α := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBA hxn) hdn) hαn

private theorem renormalisedGamma_action_constant_bound {A U n : ℝ}
    (hA : 0 ≤ A) (hU : 1 ≤ U) (hn : 0 ≤ n) :
    (1 + 4 * (A * U)) + n * (1 + 4 * (A * U)) ^ 2 +
        n ^ 2 * (1 + 4 * (A * U)) ^ 3 ≤
      ((1 + 4 * A) + n * (1 + 4 * A) ^ 2 +
        n ^ 2 * (1 + 4 * A) ^ 3) * U ^ 3 := by
  let P : ℝ := 1 + 4 * A
  let Q : ℝ := 1 + 4 * (A * U)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hQP : Q ≤ P * U := by
    dsimp [Q, P]
    calc
      1 + 4 * (A * U) ≤ U + 4 * (A * U) := by linarith
      _ = (1 + 4 * A) * U := by ring
  have hQ2 : Q ^ 2 ≤ (P * U) ^ 2 := pow_le_pow_left₀ hQ hQP 2
  have hQ3 : Q ^ 3 ≤ (P * U) ^ 3 := pow_le_pow_left₀ hQ hQP 3
  have hU2 : U ^ 2 ≤ U ^ 3 := pow_le_pow_right₀ hU (by norm_num)
  have hU1 : U ≤ U ^ 3 := by
    simpa only [pow_one] using
      (pow_le_pow_right₀ hU (show (1 : ℕ) ≤ 3 by norm_num))
  have h1 : P * U ≤ P * U ^ 3 := mul_le_mul_of_nonneg_left hU1 hP
  have h2 : n * (P * U) ^ 2 ≤ n * P ^ 2 * U ^ 3 := by
    rw [mul_pow]
    calc
      _ = n * P ^ 2 * U ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hU2 (mul_nonneg hn (sq_nonneg P))
  have h3 : n ^ 2 * (P * U) ^ 3 = n ^ 2 * P ^ 3 * U ^ 3 := by
    rw [mul_pow]
    ring
  calc
    _ ≤ P * U + n * (P * U) ^ 2 + n ^ 2 * (P * U) ^ 3 :=
      add_le_add (add_le_add hQP (mul_le_mul_of_nonneg_left hQ2 hn))
        (mul_le_mul_of_nonneg_left hQ3 (sq_nonneg n))
    _ ≤ P * U ^ 3 + n * P ^ 2 * U ^ 3 + n ^ 2 * P ^ 3 * U ^ 3 :=
      add_le_add (add_le_add h1 h2) (le_of_eq h3)
    _ = (P + n * P ^ 2 + n ^ 2 * P ^ 3) * U ^ 3 := by ring

private theorem eq_of_parabolicNorm_sub_eq_zero_renormalised
    {x y : ParabolicSpace} (h : parabolicNorm (y - x) = 0) : y = x := by
  unfold parabolicNorm at h
  have h1 : 0 ≤ Real.sqrt |(y - x).1| := Real.sqrt_nonneg _
  have h2 : 0 ≤ ∑ i, |(y - x).2 i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h3 : Real.sqrt |(y - x).1| = 0 := by linarith
  have h4 : ∑ i, |(y - x).2 i| = 0 := by linarith
  have h5 : (y - x).1 = 0 :=
    abs_eq_zero.1 ((Real.sqrt_eq_zero (abs_nonneg _)).1 h3)
  have h6 : ∀ i, (y - x).2 i = 0 := fun i =>
    abs_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg fun _ _ => abs_nonneg _).1 h4 i
      (Finset.mem_univ i))
  exact sub_eq_zero.1 (Prod.ext h5 (funext h6))

private theorem renormalisedGamma_primitive_growth
    (N : ℕ) (κ : Kappa) (noise : CanonicalNoise) (Cg : ℝ) (q : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q)
    (C : RenormalisationConstants) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ r s : ℕ, ∀ x y,
      (∀ i : Fin 4, |((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGammaParameter C y x).shift i| ≤
        A * (1 + parabolicNorm x) ^ r * (1 + parabolicNorm (y - x)) ^ s *
          parabolicNorm (y - x) ^ (parabolicWeight i : ℝ)) ∧
      |((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGammaParameter C y x).cPsi| ≤
        A * (1 + parabolicNorm x) ^ r * (1 + parabolicNorm (y - x)) ^ s *
          parabolicNorm (y - x) ^ homogeneity κ .iPsi ∧
      (∀ i : Fin 3, |((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGammaParameter C y x).cPsiGrad i| ≤
        A * (1 + parabolicNorm x) ^ r * (1 + parabolicNorm (y - x)) ^ s *
          parabolicNorm (y - x) ^ (homogeneity κ .iPsi - 1)) ∧
      |((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGammaParameter C y x).cPsiSq| ≤
        A * (1 + parabolicNorm x) ^ r * (1 + parabolicNorm (y - x)) ^ s *
          parabolicNorm (y - x) ^ homogeneity κ .iPsiSq ∧
      |((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGammaParameter C y x).cPsiCube| ≤
        A * (1 + parabolicNorm x) ^ r * (1 + parabolicNorm (y - x)) ^ s *
          parabolicNorm (y - x) ^ homogeneity κ .iPsiCube := by
  let D := hairerCanonicalData (κ := κ) N noise
  have hαPsi : 0 ≤ homogeneity κ .iPsi := by
    simp only [homogeneity]
    linarith [κ.2.1, κ.2.2]
  have hαGrad : 0 ≤ homogeneity κ .iPsi - 1 := by
    simp only [homogeneity]
    linarith [κ.2.1, κ.2.2]
  have hαSq : 0 ≤ homogeneity κ .iPsiSq := by
    simp only [homogeneity]
    linarith [κ.2.1, κ.2.2]
  have hαCube : 0 ≤ homogeneity κ .iPsiCube := by
    simp only [homogeneity]
    linarith [κ.2.1, κ.2.2]
  obtain ⟨BLp, hBLp, rLp, hLp⟩ := canonicalGamma_cPsi_growth N κ noise Cg q hg
  obtain ⟨BG, hBG, rG, sG, hG⟩ :=
    canonicalPi_global_polynomial_envelope N κ noise Cg q hg
  have hPsi : ∃ B : ℝ, 0 ≤ B ∧ ∃ r s : ℕ, ∀ x y,
      |(D.renormalisedExtensionGammaParameter C y x).cPsi| ≤
        B * (1 + parabolicNorm x) ^ r * (1 + parabolicNorm (y - x)) ^ s *
          parabolicNorm (y - x) ^ homogeneity κ .iPsi := by
    refine ⟨BLp + BG, add_nonneg hBLp hBG, rLp + rG + sG, sG, ?_⟩
    apply combine_local_global_bound_fixed hαPsi hBLp hBG
    · intro x y hxy
      simpa only [D, renormalisedGamma_cPsi_eq_canonical] using hLp x y hxy
    · intro x y
      rw [renormalisedGamma_cPsi_eq_canonical]
      rw [canonicalGamma_cPsi_eq_iPsi]
      simpa only [D] using hG .iPsi x y
  have hgradLocal : ∃ BL : ℝ, 0 ≤ BL ∧ ∃ r : ℕ, ∀ i x y,
      parabolicNorm (y - x) ≤ 1 →
        |(D.renormalisedExtensionGammaParameter C y x).cPsiGrad i| ≤
          BL * (1 + parabolicNorm x) ^ r *
            parabolicNorm (y - x) ^ (homogeneity κ .iPsi - 1) := by
    obtain ⟨B, hB, r, h⟩ := canonicalGamma_cPsiGrad_growth N κ noise Cg q hg
    refine ⟨B, hB, r, ?_⟩
    intro i x y hxy
    rw [renormalisedGamma_cPsiGrad_eq_canonical]
    exact h i x y hxy
  have hgradGlobal : ∃ BG0 : ℝ, 0 ≤ BG0 ∧ ∃ rG0 sG0 : ℕ, ∀ i x y,
      |(D.renormalisedExtensionGammaParameter C y x).cPsiGrad i| ≤
        BG0 * (1 + parabolicNorm x) ^ rG0 *
          (1 + parabolicNorm y) ^ sG0 := by
    have hchar : ∀ i : Fin 3, PolyBounded (fun z =>
        (D.canonicalCharacter z).cPsiGrad i) := by
      intro i
      have h := canonicalStructureGroup_coeff_growth N κ noise Cg q hg .iPsi (.x i)
      have he : (fun z => structureGroupMap (D.canonicalCharacter z)
          (basis .iPsi) (.x i)) = fun z => (D.canonicalCharacter z).cPsiGrad i := by
        funext z
        simp [structureBasisAction, primitiveAction, basis, Finsupp.single_apply]
      rw [he] at h
      exact h
    obtain ⟨B, hB0, r, hcharBound⟩ :=
      canonicalPolyBounded_finite_envelope (fun i : Fin 3 => fun z =>
        (D.canonicalCharacter z).cPsiGrad i) (hchar)
    refine ⟨2 * B, by positivity, 2 * r, r, ?_⟩
    intro i x y
    rw [renormalisedGamma_cPsiGrad_eq_canonical,
      canonicalGamma_cPsiGrad_eq_character_sub]
    have hh := finite_two_point_global_family
      (fun i : Fin 3 => fun z => (D.canonicalCharacter z).cPsiGrad i)
      hB0 hcharBound i x y
    have hbase : 1 + parabolicNorm (y - x) ≤
        (1 + parabolicNorm x) * (1 + parabolicNorm y) := by
      have htri : parabolicNorm (y - x) ≤ parabolicNorm y + parabolicNorm x := by
        simpa [sub_eq_add_neg, parabolicNorm_neg] using parabolicNorm_add_le y (-x)
      nlinarith [parabolicNorm_nonneg x, parabolicNorm_nonneg y]
    have hp := pow_le_pow_left₀
      (by linarith [parabolicNorm_nonneg (y - x)]) hbase r
    rw [mul_pow] at hp
    calc
      _ ≤ 2 * B * (1 + parabolicNorm x) ^ r *
          (1 + parabolicNorm (y - x)) ^ r := by
        simpa only [abs_sub_comm] using hh
      _ ≤ 2 * B * (1 + parabolicNorm x) ^ r *
          ((1 + parabolicNorm x) ^ r * (1 + parabolicNorm y) ^ r) :=
        mul_le_mul_of_nonneg_left hp
          (mul_nonneg (by positivity)
            (pow_nonneg (by linarith [parabolicNorm_nonneg x]) _))
      _ = 2 * B * (1 + parabolicNorm x) ^ (2 * r) *
          (1 + parabolicNorm y) ^ r := by
        calc
          _ = 2 * B * ((1 + parabolicNorm x) ^ r *
              (1 + parabolicNorm x) ^ r) * (1 + parabolicNorm y) ^ r := by ring
          _ = _ := by rw [← pow_add, show r + r = 2 * r by omega]
  have hgrad : ∃ BG' : ℝ, 0 ≤ BG' ∧ ∃ r s : ℕ, ∀ i x y,
      |(D.renormalisedExtensionGammaParameter C y x).cPsiGrad i| ≤
        BG' * (1 + parabolicNorm x) ^ r * (1 + parabolicNorm (y - x)) ^ s *
          parabolicNorm (y - x) ^ (homogeneity κ .iPsi - 1) := by
    obtain ⟨BL, hBL, rL, hL⟩ := hgradLocal
    obtain ⟨BG0, hBG0, rG0, sG0, hG0⟩ := hgradGlobal
    refine ⟨BL + BG0, add_nonneg hBL hBG0, rL + rG0 + sG0, sG0, ?_⟩
    intro i x y
    apply combine_local_global_bound_fixed (F := fun x y =>
      (D.renormalisedExtensionGammaParameter C y x).cPsiGrad i)
      (α := homogeneity κ .iPsi - 1) (Bl := BL) (Bg := BG0)
      (rl := rL) (rg := rG0) (sg := sG0) hαGrad hBL hBG0
    · intro x y hxy
      simpa only [pow_zero, one_mul, pow_one, mul_one] using hL i x y hxy
    · intro x y
      exact hG0 i x y
  have hpositive : 0 < homogeneity κ .iPsiSq ∧ 0 < homogeneity κ .iPsiCube := by
    constructor <;> simp only [homogeneity] <;> linarith [κ.2.1, κ.2.2]
  have hcutSq : homogeneity κ .iPsiSq < gamma κ := by
    simp only [homogeneity, gamma]
    linarith [κ.2.1]
  have hcutCube : homogeneity κ .iPsiCube < gamma κ := by
    simp only [homogeneity, gamma]
    linarith [κ.2.1]
  obtain ⟨BIncSq, hBIncSq, rIncSq, hIncSq⟩ :=
    canonicalPi_positive_increment_envelope N κ noise Cg q hg
  obtain ⟨BIncCube, hBIncCube, rIncCube, hIncCube⟩ :=
    renormalisedExtensionPi_positive_increment_envelope N κ noise Cg q hg C
  have hsqLocal : ∀ x y, parabolicNorm (y - x) ≤ 1 →
      |(D.renormalisedExtensionGammaParameter C y x).cPsiSq| ≤
        BIncSq * (1 + parabolicNorm x) ^ rIncSq *
          parabolicNorm (y - x) ^ homogeneity κ .iPsiSq := by
    intro x y hxy
    rw [renormalisedGamma_cPsiSq_eq_canonical, canonicalGamma_cPsiSq_eq_iPsiSq]
    have hh := hIncSq .iPsiSq hpositive.1 x y hxy
    have hα1 : homogeneity κ .iPsiSq ≤ 1 := by
      simp only [homogeneity]
      linarith [κ.2.1]
    have hd : parabolicNorm (y - x) ≤
        parabolicNorm (y - x) ^ homogeneity κ .iPsiSq := by
      simpa only [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_ge' (parabolicNorm_nonneg _) hxy hαSq hα1)
    exact hh.trans (mul_le_mul_of_nonneg_left hd
      (mul_nonneg hBIncSq (pow_nonneg (by linarith [parabolicNorm_nonneg x]) _)))
  have hcubeLocal : ∀ x y, parabolicNorm (y - x) ≤ 1 →
      |(D.renormalisedExtensionGammaParameter C y x).cPsiCube| ≤
        BIncCube * (1 + parabolicNorm x) ^ rIncCube *
          parabolicNorm (y - x) ^ homogeneity κ .iPsiCube := by
    intro x y hxy
    rw [renormalisedGamma_cPsiCube_eq N κ noise C x y]
    have hh := hIncCube .iPsiCube hpositive.2 x y hxy
    have hα1 : homogeneity κ .iPsiCube ≤ 1 := by
      simp only [homogeneity]
      linarith [κ.2.1]
    have hd : parabolicNorm (y - x) ≤
        parabolicNorm (y - x) ^ homogeneity κ .iPsiCube := by
      simpa only [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_ge' (parabolicNorm_nonneg _) hxy hαCube hα1)
    exact hh.trans (mul_le_mul_of_nonneg_left hd
      (mul_nonneg hBIncCube (pow_nonneg (by linarith [parabolicNorm_nonneg x]) _)))
  have hSqBound : ∃ BS : ℝ, 0 ≤ BS ∧ ∃ rS sS : ℕ, ∀ x y,
      |(D.renormalisedExtensionGammaParameter C y x).cPsiSq| ≤
        BS * (1 + parabolicNorm x) ^ rS * (1 + parabolicNorm (y - x)) ^ sS *
          parabolicNorm (y - x) ^ homogeneity κ .iPsiSq := by
    refine ⟨BIncSq + BG, add_nonneg hBIncSq hBG, rIncSq + rG + sG, sG, ?_⟩
    apply combine_local_global_bound_fixed (F := fun x y =>
      (D.renormalisedExtensionGammaParameter C y x).cPsiSq)
      (α := homogeneity κ .iPsiSq) (Bl := BIncSq) (Bg := BG)
      (rl := rIncSq) (rg := rG) (sg := sG) hαSq hBIncSq hBG hsqLocal
    intro x y
    rw [renormalisedGamma_cPsiSq_eq_canonical, canonicalGamma_cPsiSq_eq_iPsiSq]
    simpa only [D] using hG .iPsiSq x y
  obtain ⟨BS, hBS, rS, sS, hSq⟩ := hSqBound
  have hCubeBound : ∃ BC : ℝ, 0 ≤ BC ∧ ∃ rC sC : ℕ, ∀ x y,
      |(D.renormalisedExtensionGammaParameter C y x).cPsiCube| ≤
        BC * (1 + parabolicNorm x) ^ rC * (1 + parabolicNorm (y - x)) ^ sC *
          parabolicNorm (y - x) ^ homogeneity κ .iPsiCube := by
    obtain ⟨BR, hBR, aR, bR, hR⟩ :=
      renormalisedExtensionPi_global_polynomial_envelope N κ noise Cg q hg C
    refine ⟨BIncCube + BR, add_nonneg hBIncCube hBR, rIncCube + aR + bR, bR, ?_⟩
    apply combine_local_global_bound_fixed (F := fun x y =>
      (D.renormalisedExtensionGammaParameter C y x).cPsiCube)
      (α := homogeneity κ .iPsiCube) (Bl := BIncCube) (Bg := BR)
      (rl := rIncCube) (rg := aR) (sg := bR) hαCube hBIncCube hBR hcubeLocal
    intro x y
    rw [renormalisedGamma_cPsiCube_eq N κ noise C x y]
    simpa only [D] using hR .iPsiCube x y
  obtain ⟨BC, hBC, rC, sC, hCube⟩ := hCubeBound
  obtain ⟨BP, hBP, rP, sP, hP⟩ := hPsi
  obtain ⟨BG', hBG', rG', sG', hG'⟩ := hgrad
  let A := 1 + BP + BG' + BS + BC
  let R := rP + rG' + rS + rC
  let S := sP + sG' + sS + sC
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hAone : 1 ≤ A := by dsimp [A]; linarith
  refine ⟨A, hA0, R, S, ?_⟩
  intro x y
  constructor
  · intro i
    have hp := canonicalGamma_shift_bound N κ noise x y i
    have hfac : 1 ≤ A * (1 + parabolicNorm x) ^ R *
        (1 + parabolicNorm (y - x)) ^ S := by
      have hx : 1 ≤ (1 + parabolicNorm x) ^ R :=
        one_le_pow₀ (by linarith [parabolicNorm_nonneg x])
      have hd : 1 ≤ (1 + parabolicNorm (y - x)) ^ S :=
        one_le_pow₀ (by linarith [parabolicNorm_nonneg (y - x)])
      exact (hAone.trans (le_mul_of_one_le_right hA0 hx)).trans
        (le_mul_of_one_le_right
          (mul_nonneg hA0
            (pow_nonneg (by linarith [parabolicNorm_nonneg x]) _)) hd)
    exact hp.trans (by
      calc
        _ ≤ parabolicNorm (y - x) ^ (parabolicWeight i : ℝ) *
            (A * (1 + parabolicNorm x) ^ R *
              (1 + parabolicNorm (y - x)) ^ S) :=
          le_mul_of_one_le_right
            (Real.rpow_nonneg (parabolicNorm_nonneg _) _) hfac
        _ = _ := by ring)
  · constructor
    · exact enlarge_weighted_bound (F := fun x y =>
          (D.renormalisedExtensionGammaParameter C y x).cPsi)
        hαPsi hBP
        (by change BP ≤ 1 + BP + BG' + BS + BC; linarith)
        (by change rP ≤ rP + rG' + rS + rC; omega)
        (by change sP ≤ sP + sG' + sS + sC; omega) x y (hP x y)
    · constructor
      · intro i
        exact enlarge_weighted_bound (F := fun x y =>
            (D.renormalisedExtensionGammaParameter C y x).cPsiGrad i)
          hαGrad hBG'
          (by change BG' ≤ 1 + BP + BG' + BS + BC; linarith)
          (by change rG' ≤ rP + rG' + rS + rC; omega)
          (by change sG' ≤ sP + sG' + sS + sC; omega) x y (hG' i x y)
      · constructor
        · exact enlarge_weighted_bound (F := fun x y =>
              (D.renormalisedExtensionGammaParameter C y x).cPsiSq)
            hαSq hBS
            (by change BS ≤ 1 + BP + BG' + BS + BC; linarith)
            (by change rS ≤ rP + rG' + rS + rC; omega)
            (by change sS ≤ sP + sG' + sS + sC; omega) x y (hSq x y)
        · exact enlarge_weighted_bound (F := fun x y =>
              (D.renormalisedExtensionGammaParameter C y x).cPsiCube)
            hαCube hBC
            (by change BC ≤ 1 + BP + BG' + BS + BC; linarith)
            (by change rC ≤ rP + rG' + rS + rC; omega)
            (by change sC ≤ sP + sG' + sS + sC; omega) x y (hCube x y)

theorem canonicalRenormalisedModel_gammaBoundGrowth
    (N : ℕ) (κ : Kappa) (noise : CanonicalNoise) (C : ℝ) (p : ℕ)
    (hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ C * (1 + parabolicNorm z) ^ p)
    (c : RenormalisationConstants) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ r q : ℕ,
      (canonicalRenormalisedModel N κ noise C p hg c).GammaBoundGrowth (gamma κ) B
        (parabolicPolynomialWeight (r : ℝ)) (q : ℝ) := by
  obtain ⟨A, hA, r, s, hprim⟩ := renormalisedGamma_primitive_growth N κ noise C p hg c
  let n : ℝ := (Fintype.card Symbol : ℝ) ^ 2
  let C₀ : ℝ := (1 + 4 * A) + n * (1 + 4 * A) ^ 2 +
    n ^ 2 * (1 + 4 * A) ^ 3
  have hn : 0 ≤ n := by dsimp [n]; positivity
  have hC₀ : 0 ≤ C₀ := by
    dsimp [C₀]
    positivity
  refine ⟨C₀, hC₀, 3 * r, 3 * s, ?_⟩
  intro τ σ hτ hστ x y
  change homogeneity κ τ < gamma κ at hτ
  change homogeneity κ σ < homogeneity κ τ at hστ
  let g := (hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGammaParameter c y x
  change |(phi43StructureGroupElement g : (Symbol → ℝ) →ₗ[ℝ] (Symbol → ℝ))
      (Pi.single τ 1) σ| ≤ _
  rw [phi43StructureGroupElement_apply_single]
  change |structureGroupMap g (basis τ) σ| ≤ _
  let d : ℝ := parabolicNorm (y - x)
  have hδ : 0 < homogeneity κ τ - homogeneity κ σ := sub_pos.mpr hστ
  by_cases hd : d = 0
  · have hxy : y = x := eq_of_parabolicNorm_sub_eq_zero_renormalised hd
    subst y
    change |(hairerCanonicalData (κ := κ) N noise).renormalisedExtensionGamma c x x
        (basis τ) σ| ≤ _
    rw [CanonicalData.renormalisedExtensionGamma_self]
    have hne : τ ≠ σ := by
      intro h
      subst σ
      exact (lt_irrefl _ hστ)
    change |phi43CoordinateEquiv (basis τ) σ| ≤
      C₀ * parabolicPolynomialWeight ((3 * r : ℕ) : ℝ) x *
        (1 + parabolicNorm (x - x)) ^ ((3 * s : ℕ) : ℝ) *
        parabolicNorm (x - x) ^ (homogeneity κ τ - homogeneity κ σ)
    rw [phi43CoordinateEquiv_basis]
    simp [hne, Real.zero_rpow hδ.ne']
  · have hdpos : 0 < d := lt_of_le_of_ne (parabolicNorm_nonneg _) (Ne.symm hd)
    let X : ℝ := 1 + parabolicNorm x
    let Dd : ℝ := 1 + d
    let U : ℝ := X ^ r * Dd ^ s
    have hXone : 1 ≤ X ^ r := by
      apply one_le_pow₀
      dsimp [X]
      linarith [parabolicNorm_nonneg x]
    have hDone : 1 ≤ Dd ^ s := by
      apply one_le_pow₀
      dsimp [Dd]
      linarith [parabolicNorm_nonneg (y - x)]
    have hUone : 1 ≤ U := by
      dsimp [U]
      exact one_le_mul_of_one_le_of_one_le hXone hDone
    have hAout : 0 ≤ A * U := mul_nonneg hA (by positivity)
    have hshift (i : Fin 4) : |g.shift i| ≤
        (A * U) * d ^ (parabolicWeight i : ℝ) := by
      simpa [g, U, X, Dd, d, mul_assoc, mul_left_comm, mul_comm] using
        (hprim x y).1 i
    have hp : |g.cPsi| ≤ (A * U) * d ^ homogeneity κ .iPsi := by
      simpa [g, U, X, Dd, d, mul_assoc, mul_left_comm, mul_comm] using
        (hprim x y).2.1
    have hpg (i : Fin 3) : |g.cPsiGrad i| ≤
        (A * U) * d ^ (homogeneity κ .iPsi - 1) := by
      simpa [g, U, X, Dd, d, mul_assoc, mul_left_comm, mul_comm] using
        (hprim x y).2.2.1 i
    have hs : |g.cPsiSq| ≤ (A * U) * d ^ homogeneity κ .iPsiSq := by
      simpa [g, U, X, Dd, d, mul_assoc, mul_left_comm, mul_comm] using
        (hprim x y).2.2.2.1
    have hc : |g.cPsiCube| ≤ (A * U) * d ^ homogeneity κ .iPsiCube := by
      simpa [g, U, X, Dd, d, mul_assoc, mul_left_comm, mul_comm] using
        (hprim x y).2.2.2.2
    have hact := gammaStructureBasis_weighted_bound κ g hdpos hAout hshift hp hpg hs hc τ σ
    have hcoeff :
        (1 + 4 * (A * U)) + n * (1 + 4 * (A * U)) ^ 2 +
            n ^ 2 * (1 + 4 * (A * U)) ^ 3 ≤ C₀ * U ^ 3 := by
      exact renormalisedGamma_action_constant_bound hA hUone hn
    have hU3 : U ^ 3 =
        (1 + parabolicNorm x) ^ (3 * r) *
          (1 + parabolicNorm (y - x)) ^ (3 * s) := by
      dsimp [U, X, Dd, d]
      calc
        ((1 + parabolicNorm x) ^ r *
            (1 + parabolicNorm (y - x)) ^ s) ^ 3 =
            ((1 + parabolicNorm x) ^ r) ^ 3 *
              ((1 + parabolicNorm (y - x)) ^ s) ^ 3 := by rw [mul_pow]
        _ = (1 + parabolicNorm x) ^ (r * 3) *
              (1 + parabolicNorm (y - x)) ^ (s * 3) := by
          rw [pow_mul, pow_mul]
        _ = (1 + parabolicNorm x) ^ (3 * r) *
              (1 + parabolicNorm (y - x)) ^ (3 * s) := by
          rw [Nat.mul_comm r 3, Nat.mul_comm s 3]
    rw [structureGroupMap_basis]
    have hact' : |structureBasisAction g τ σ| ≤ C₀ * U ^ 3 *
        d ^ (homogeneity κ τ - homogeneity κ σ) := by
      calc
        |structureBasisAction g τ σ| ≤
            ((1 + 4 * (A * U)) + n * (1 + 4 * (A * U)) ^ 2 +
              n ^ 2 * (1 + 4 * (A * U)) ^ 3) *
              d ^ (homogeneity κ τ - homogeneity κ σ) := by
                simpa [n] using hact
        _ ≤ C₀ * U ^ 3 * d ^ (homogeneity κ τ - homogeneity κ σ) := by
          exact mul_le_mul_of_nonneg_right hcoeff
            (Real.rpow_nonneg hdpos.le _)
    calc
      |structureBasisAction g τ σ| ≤ C₀ * U ^ 3 *
          d ^ (homogeneity κ τ - homogeneity κ σ) := hact'
      _ = C₀ * parabolicPolynomialWeight ((3 * r : ℕ) : ℝ) x *
          (1 + parabolicNorm (y - x)) ^ ((3 * s : ℕ) : ℝ) *
          parabolicNorm (y - x) ^ (homogeneity κ τ - homogeneity κ σ) := by
        rw [hU3]
        simp only [parabolicPolynomialWeight, Real.rpow_natCast]
        ring

end RegularityStructures.Phi43

end
