/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.RegularisedNoise.SmoothVersion.CoefficientDecay

/-!
# Weighted lattice summability from smooth Fourier decay

This module records the weighted form of the finite-window Fourier summability estimate.  It is
used for derivatives of the translated Fourier characters: a coefficient estimate with two extra
powers for each polynomial weight gives absolute summability after that weight is applied.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace RegularityStructures.Phi43

theorem summable_smoothVersion_fourier_weighted_of_coordinate_decay
    {A : (Fin 4 → ℤ) → ℂ} (q : ℕ)
    (hzero : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ‖A 0‖ ≤ C₀)
    (hcoord : ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : Fin 4, ∀ k : Fin 4 → ℤ, k i ≠ 0 →
        ‖A k‖ ≤ C * |(k i : ℝ)|⁻¹ ^ (6 + 2 * q : ℕ)) :
    Summable (fun k : Fin 4 → ℤ =>
      smoothVersionFrequencyNormSq k ^ q * ‖A k‖) := by
  obtain ⟨C₀, hC₀, hA₀⟩ := hzero
  obtain ⟨C, hC, hcoord⟩ := hcoord
  let B : (Fin 4 → ℤ) → ℂ := fun k =>
    (smoothVersionFrequencyNormSq k ^ q : ℂ) * A k
  have hBzero : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ‖B 0‖ ≤ C₀ := by
    refine ⟨C₀, hC₀, ?_⟩
    have hS0 : smoothVersionFrequencyNormSq 0 = 1 := by
      simp [smoothVersionFrequencyNormSq]
    simp [B, hS0, hA₀]
  have hBcoord : ∃ C' : ℝ, 0 ≤ C' ∧
      ∀ i : Fin 4, ∀ k : Fin 4 → ℤ, k i ≠ 0 →
        ‖B k‖ ≤ C' * |(k i : ℝ)|⁻¹ ^ (6 : ℕ) := by
    refine ⟨5 ^ q * C, by positivity, ?_⟩
    intro i k hki
    obtain ⟨j, hj, hMj⟩ := Finset.exists_mem_eq_sup'
      (s := (Finset.univ : Finset (Fin 4))) Finset.univ_nonempty
      (fun j => |(k j : ℝ)|)
    let M : ℝ := (Finset.univ : Finset (Fin 4)).sup'
      Finset.univ_nonempty (fun j => |(k j : ℝ)|)
    have hMbound : ∀ l : Fin 4, |(k l : ℝ)| ≤ M := by
      intro l
      exact Finset.le_sup' (fun r => |(k r : ℝ)|) (Finset.mem_univ l)
    have hMone : (1 : ℝ) ≤ M := by
      have hki_int : (1 : ℤ) ≤ |k i| := Int.one_le_abs hki
      have hki_one : (1 : ℝ) ≤ |(k i : ℝ)| := by
        exact_mod_cast hki_int
      exact hki_one.trans (hMbound i)
    have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hMone
    have hsum_le : ∑ l : Fin 4, ((k l : ℝ)) ^ 2 ≤ 4 * M ^ 2 := by
      calc
        ∑ l : Fin 4, ((k l : ℝ)) ^ 2 ≤ ∑ l : Fin 4, M ^ 2 := by
          apply Finset.sum_le_sum
          intro l hl
          have hle : |(k l : ℝ)| ≤ |M| := by
            rw [abs_of_pos hMpos]
            exact hMbound l
          simpa using (sq_le_sq.mpr hle)
        _ = 4 * M ^ 2 := by norm_num
    have hSbound : smoothVersionFrequencyNormSq k ≤ 5 * M ^ 2 := by
      dsimp [smoothVersionFrequencyNormSq]
      nlinarith [sq_nonneg M, hsum_le]
    have hSq_nonneg : 0 ≤ smoothVersionFrequencyNormSq k := by
      dsimp [smoothVersionFrequencyNormSq]
      have hs : 0 ≤ ∑ l : Fin 4, ((k l : ℝ)) ^ 2 :=
        Finset.sum_nonneg fun l _ => sq_nonneg _
      linarith
    have hS_pow : smoothVersionFrequencyNormSq k ^ q ≤
        (5 ^ q : ℝ) * M ^ (2 * q) := by
      calc
        smoothVersionFrequencyNormSq k ^ q ≤ (5 * M ^ 2) ^ q :=
          pow_le_pow_left₀ hSq_nonneg hSbound q
        _ = (5 ^ q : ℝ) * M ^ (2 * q) := by ring
    have hA : ‖A k‖ ≤ C * M⁻¹ ^ (6 + 2 * q : ℕ) := by
      calc
        ‖A k‖ ≤ C * |(k j : ℝ)|⁻¹ ^ (6 + 2 * q : ℕ) := by
          apply hcoord j k
          intro hj0
          have : M = 0 := by simpa [M, hj0] using hMj
          linarith
        _ = C * M⁻¹ ^ (6 + 2 * q : ℕ) := by
          rw [← hMj]
    have hnormB : ‖B k‖ = smoothVersionFrequencyNormSq k ^ q * ‖A k‖ := by
      change ‖(smoothVersionFrequencyNormSq k ^ q : ℂ) * A k‖ = _
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hSq_nonneg]
    rw [hnormB]
    calc
      smoothVersionFrequencyNormSq k ^ q * ‖A k‖ ≤
          smoothVersionFrequencyNormSq k ^ q * (C * M⁻¹ ^ (6 + 2 * q : ℕ)) :=
        mul_le_mul_of_nonneg_left hA (by positivity)
      _ ≤ (5 ^ q * C) * M⁻¹ ^ (6 : ℕ) := by
        have hMpow : M ^ (2 * q) * M⁻¹ ^ (6 + 2 * q : ℕ) = M⁻¹ ^ (6 : ℕ) := by
          calc
            M ^ (2 * q) * M⁻¹ ^ (6 + 2 * q : ℕ) =
                M ^ (2 * q) * (M ^ (6 + 2 * q : ℕ))⁻¹ := by
                  rw [inv_pow]
            _ = M ^ (2 * q) / M ^ (6 + 2 * q : ℕ) := by
                  rw [div_eq_mul_inv]
            _ = (M ^ (6 : ℕ))⁻¹ := by
                  field_simp [ne_of_gt hMpos]
                  ring
            _ = M⁻¹ ^ (6 : ℕ) := by rw [inv_pow]
        calc
          smoothVersionFrequencyNormSq k ^ q * (C * M⁻¹ ^ (6 + 2 * q : ℕ)) =
              C * (smoothVersionFrequencyNormSq k ^ q *
                M⁻¹ ^ (6 + 2 * q : ℕ)) := by ring
          _ ≤ C * ((5 ^ q : ℝ) * M ^ (2 * q) *
                M⁻¹ ^ (6 + 2 * q : ℕ)) := by
              apply mul_le_mul_of_nonneg_left
              · exact mul_le_mul_of_nonneg_right hS_pow (by positivity)
              · exact hC
          _ = (5 ^ q * C) * M⁻¹ ^ (6 : ℕ) := by
            calc
              C * (5 ^ q * M ^ (2 * q) * M⁻¹ ^ (6 + 2 * q : ℕ)) =
                  5 ^ q * C * (M ^ (2 * q) * M⁻¹ ^ (6 + 2 * q : ℕ)) := by ring
              _ = (5 ^ q * C) * M⁻¹ ^ (6 : ℕ) := by rw [hMpow]
      _ ≤ (5 ^ q * C) * |(k i : ℝ)|⁻¹ ^ (6 : ℕ) := by
        have hi_pos : 0 < |(k i : ℝ)| := abs_pos.mpr (by exact_mod_cast hki)
        have hinv : M⁻¹ ≤ |(k i : ℝ)|⁻¹ :=
          (inv_le_inv₀ hMpos hi_pos).2 (hMbound i)
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hinv 6) (by positivity)
  have hBsum := summable_smoothVersion_fourier_of_coordinate_decay hBzero hBcoord
  apply hBsum.congr
  intro k
  change ‖(smoothVersionFrequencyNormSq k ^ q : ℂ) * A k‖ = _
  have hkS : 0 ≤ smoothVersionFrequencyNormSq k := by
    dsimp [smoothVersionFrequencyNormSq]
    have hs : 0 ≤ ∑ i : Fin 4, ((k i : ℝ)) ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    linarith
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hkS]

end RegularityStructures.Phi43

end
