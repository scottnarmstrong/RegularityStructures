/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.RegularisedNoise.SmoothVersion.LatticeSummability

/-!
# Summability from coordinatewise Fourier decay

On the four-dimensional finite-window frequency lattice, decay in a coordinate of maximal
magnitude is enough for absolute summability.  This is the lattice bookkeeping used after the
coordinatewise integration-by-parts estimate.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace RegularityStructures.Phi43

def smoothVersionFrequencyNormSq (k : Fin 4 → ℤ) : ℝ :=
  1 + ∑ i, ((k i : ℝ)) ^ 2

theorem summable_smoothVersion_fourier_of_coordinate_decay
    {A : (Fin 4 → ℤ) → ℂ}
    (hzero : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ‖A 0‖ ≤ C₀)
    (hcoord : ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : Fin 4, ∀ k : Fin 4 → ℤ, k i ≠ 0 →
        ‖A k‖ ≤ C * |(k i : ℝ)|⁻¹ ^ (6 : ℕ)) :
    Summable (fun k : Fin 4 → ℤ => ‖A k‖) := by
  obtain ⟨C₀, hC₀, hA₀⟩ := hzero
  obtain ⟨C, hC, hcoord⟩ := hcoord
  let weight : (Fin 4 → ℤ) → ℝ := fun k =>
    (smoothVersionFrequencyNormSq k ^ (3 : ℕ))⁻¹
  have hweight : Summable weight := by
    simpa [weight, smoothVersionFrequencyNormSq] using
      (summable_smoothVersion_inv_one_add_normSq_pow (d := 4) (r := 3) (by norm_num))
  let B : ℝ := max C₀ (125 * C)
  have hB : 0 ≤ B := by
    exact hC₀.trans (le_max_left _ _)
  have hA_sum : Summable A := by
    refine Summable.of_norm_bounded (hweight.mul_left B) ?_
    intro k
    by_cases hk : k = 0
    · rw [hk]
      have hB0 : C₀ ≤ B := by
        dsimp [B]
        exact le_max_left _ _
      have hw0 : weight 0 = 1 := by
        simp [weight, smoothVersionFrequencyNormSq]
      rw [hw0, mul_one]
      exact hA₀.trans hB0
    · obtain ⟨j, hj⟩ : ∃ j : Fin 4, k j ≠ 0 := by
        contrapose! hk
        funext i
        exact hk i
      let M : ℝ := (Finset.univ : Finset (Fin 4)).sup'
        Finset.univ_nonempty (fun i => |(k i : ℝ)|)
      obtain ⟨i, hi, hMi⟩ := Finset.exists_mem_eq_sup'
        (s := (Finset.univ : Finset (Fin 4))) Finset.univ_nonempty
        (fun i => |(k i : ℝ)|)
      change M = |(k i : ℝ)| at hMi
      have hM_j : |(k j : ℝ)| ≤ M := by
        exact Finset.le_sup' (fun i => |(k i : ℝ)|) (Finset.mem_univ j)
      have hM_one : 1 ≤ M := by
        have hcast : (1 : ℝ) ≤ |(k j : ℝ)| := by
          have hInt : (1 : ℤ) ≤ |k j| := Int.one_le_abs hj
          exact_mod_cast hInt
        exact hcast.trans hM_j
      have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM_one
      have hi0 : k i ≠ 0 := by
        intro hi0
        have hMzero : M = 0 := by simpa [hi0] using hMi
        linarith
      have hcoord_i := hcoord i k hi0
      have hsum_le : ∑ q : Fin 4, ((k q : ℝ)) ^ 2 ≤ 4 * M ^ 2 := by
        calc
          ∑ q : Fin 4, ((k q : ℝ)) ^ 2 ≤ ∑ q : Fin 4, M ^ 2 := by
            apply Finset.sum_le_sum
            intro q hq
            have hqM : |(k q : ℝ)| ≤ M :=
              Finset.le_sup' (fun r => |(k r : ℝ)|) (Finset.mem_univ q)
            have hqM' : |(k q : ℝ)| ≤ |M| := by
              rw [abs_of_pos hMpos]
              exact hqM
            simpa using (sq_le_sq.mpr hqM')
          _ = 4 * M ^ 2 := by norm_num
      have hnormSq_le : smoothVersionFrequencyNormSq k ≤ 5 * M ^ 2 := by
        dsimp [smoothVersionFrequencyNormSq]
        nlinarith [sq_nonneg M]
      have hnormSq_nonneg : 0 ≤ smoothVersionFrequencyNormSq k := by
        dsimp [smoothVersionFrequencyNormSq]
        have hsum_nonneg : 0 ≤ ∑ q : Fin 4, ((k q : ℝ)) ^ 2 :=
          Finset.sum_nonneg fun q _ => sq_nonneg _
        linarith
      have hpow : smoothVersionFrequencyNormSq k ^ (3 : ℕ) ≤ 125 * M ^ 6 := by
        calc
          smoothVersionFrequencyNormSq k ^ (3 : ℕ) ≤ (5 * M ^ 2) ^ (3 : ℕ) := by
            exact pow_le_pow_left₀ hnormSq_nonneg hnormSq_le 3
          _ = 125 * M ^ 6 := by ring
      have hA : ‖A k‖ ≤ C * M⁻¹ ^ (6 : ℕ) := by
        calc
          ‖A k‖ ≤ C * |(k i : ℝ)|⁻¹ ^ (6 : ℕ) := hcoord_i
          _ = C * M⁻¹ ^ (6 : ℕ) := by rw [hMi]
      have hweight_pos : 0 < smoothVersionFrequencyNormSq k ^ (3 : ℕ) := by
        have hsum_nonneg : 0 ≤ ∑ q : Fin 4, ((k q : ℝ)) ^ 2 :=
          Finset.sum_nonneg fun q _ => sq_nonneg _
        have hbase_pos : 0 < smoothVersionFrequencyNormSq k := by
          dsimp [smoothVersionFrequencyNormSq]
          linarith
        exact pow_pos hbase_pos _
      have hinv : M⁻¹ ^ (6 : ℕ) ≤ 125 * weight k := by
        dsimp [weight]
        rw [inv_pow, ← one_div]
        calc
          1 / M ^ 6 = 125 / (125 * M ^ 6) := by field_simp
          _ ≤ 125 / smoothVersionFrequencyNormSq k ^ (3 : ℕ) := by
            apply (div_le_div_iff₀ (by positivity) hweight_pos).2
            nlinarith [hpow]
          _ = 125 * (smoothVersionFrequencyNormSq k ^ (3 : ℕ))⁻¹ := by
            field_simp
      calc
        ‖A k‖ ≤ C * M⁻¹ ^ (6 : ℕ) := hA
        _ ≤ (125 * C) * weight k := by
          calc
            C * M⁻¹ ^ (6 : ℕ) ≤ C * (125 * weight k) :=
              mul_le_mul_of_nonneg_left hinv hC
            _ = (125 * C) * weight k := by ring
        _ ≤ B * weight k := by
          exact mul_le_mul_of_nonneg_right (le_max_right _ _)
            (by positivity)
  exact hA_sum.norm

end RegularityStructures.Phi43

end
