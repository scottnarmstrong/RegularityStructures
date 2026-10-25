/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HolderBesovFrequencyGeometry
public import RegularityStructures.Torus.HolderBesovAnnulusGreen

/-!
# An annular reproducer for the literal dyadic blocks

For block `n+1`, the frequency lies between radii `2^n` and `2^(n+2)`. The outer cutoff at scale
`2^(n+2)` is one there; the inner cutoff dilated by eight vanishes in at least one coordinate. Their
tensor difference is therefore exactly one on the dyadic support. This is the annular multiplier
step in the equivalence of the heat norm (2.3) of the statement with the Littlewood--Paley norm.
-/

@[expose] public noncomputable section

open UnitAddTorus

namespace RegularityStructures

/-- A fixed-shape enlarged annulus, reproducing the level-`n+1` dyadic symbol. -/
def torusLPAnnulusReproducer (n : ℕ) (k : Fin 3 → ℤ) : ℝ :=
  torusLowFrequencySymbol (n + 2) k -
    ∏ i : Fin 3, torusLPBump (8 * (((2 : ℝ) ^ (n + 2))⁻¹ * (k i : ℝ)))

theorem torusLPAnnulusReproducer_eq_one (n : ℕ) (k : Fin 3 → ℤ)
    (hk : torusDyadicFrequencySymbol (n + 1) k ≠ 0) :
    torusLPAnnulusReproducer n k = 1 := by
  have hbox : k ∈ torusLPFrequencyBox (n + 1) := by
    by_contra h
    exact hk (torusDyadicFrequencySymbol_eq_zero_of_notMem_box (n + 1) k h)
  have houter : torusLowFrequencySymbol (n + 2) k = 1 := by
    apply torusLowFrequencySymbol_eq_one
    intro i
    have hi := Finset.mem_Icc.mp ((Fintype.mem_piFinset.mp hbox) i)
    apply abs_le.mpr
    constructor
    · exact_mod_cast hi.1
    · exact_mod_cast hi.2
  have hlarge : ∃ i : Fin 3, (2 : ℝ) ^ n < |(k i : ℝ)| := by
    by_contra! h
    exact hk (torusDyadicFrequencySymbol_succ_eq_zero_of_small n k h)
  obtain ⟨i, hi⟩ := hlarge
  have hinner : (∏ j : Fin 3,
      torusLPBump (8 * (((2 : ℝ) ^ (n + 2))⁻¹ * (k j : ℝ)))) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    apply torusLPBump.zero_of_le_dist
    change 2 ≤ |8 * (((2 : ℝ) ^ (n + 2))⁻¹ * (k i : ℝ)) - 0|
    rw [sub_zero, abs_mul, abs_mul, abs_inv,
      abs_of_pos (by norm_num : (0 : ℝ) < 8),
      abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) (n + 2))]
    have he : 8 * (((2 : ℝ) ^ (n + 2))⁻¹ * (2 : ℝ) ^ n) = 2 := by
      rw [pow_add]
      norm_num
    calc
      (2 : ℝ) = 8 * (((2 : ℝ) ^ (n + 2))⁻¹ * (2 : ℝ) ^ n) := he.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hi.le (inv_nonneg.mpr (pow_nonneg (by norm_num) _)))
        (by norm_num)
  rw [torusLPAnnulusReproducer, houter, hinner, sub_zero]

theorem torusDyadicFrequencySymbol_succ_reproducer (n : ℕ) (k : Fin 3 → ℤ) :
    torusLPAnnulusReproducer n k * torusDyadicFrequencySymbol (n + 1) k =
      torusDyadicFrequencySymbol (n + 1) k := by
  by_cases hk : torusDyadicFrequencySymbol (n + 1) k = 0
  · rw [hk, mul_zero]
  · rw [torusLPAnnulusReproducer_eq_one n k hk, one_mul]

end RegularityStructures

end
