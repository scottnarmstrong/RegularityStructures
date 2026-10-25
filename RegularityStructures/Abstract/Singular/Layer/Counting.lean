/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Layer.Sums

/-!
# Cardinalities of the lattice boxes of the layer bound

With `r = 2^{-n}`, `Λ = λ 2^n ≥ 32`, `R₁ = λ + 8 · 2^{-(n+1)}`:

* the boxes `latticeBox n z (144 r²) (12 r)` have at most `5097040` elements;
* the space factor of `latticeBox (n+1) x (R₁²) R₁` has at most `125 Λ³` elements and the time factor
  at most `11 Λ²` elements;
* the box `latticeBox (n+1) ξ (216 r²) R₁` has at most `1730 · 125 Λ³` elements.
-/

public section

namespace RegularityStructures.Layer

private theorem four_pow (n : ℕ) : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by
  rw [← pow_mul, mul_comm, pow_mul]; norm_num

theorem card_latticeBox_pair_le (n : ℕ) (z : ParabolicSpace) :
    ((latticeBox n z (144 * (((2 : ℝ) ^ n)⁻¹) ^ 2) (12 * ((2 : ℝ) ^ n)⁻¹)).card : ℝ) ≤
      5097040 := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have := card_latticeBox_le (n := n) (x := z) (rt := 144 * (((2 : ℝ) ^ n)⁻¹) ^ 2)
    (rs := 12 * ((2 : ℝ) ^ n)⁻¹) (by positivity) (by positivity)
  refine this.trans (le_of_eq ?_)
  rw [four_pow]
  field_simp
  norm_num

theorem two_mul_succ_le {n : ℕ} {lam : ℝ} (hΛ : 32 ≤ lam * 2 ^ n) :
    2 * (2 : ℝ) ^ (n + 1) * (lam + 8 * ((2 : ℝ) ^ (n + 1))⁻¹) + 2 ≤ 5 * (lam * 2 ^ n) := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (n + 1) := by positivity
  have e : 2 * (2 : ℝ) ^ (n + 1) * (lam + 8 * ((2 : ℝ) ^ (n + 1))⁻¹) =
      4 * (lam * 2 ^ n) + 16 := by
    rw [pow_succ]; field_simp; ring
  rw [e]; linarith

theorem card_latticeBox_time_succ_le {n : ℕ} {lam : ℝ} (hlam : 0 < lam) (hΛ : 32 ≤ lam * 2 ^ n)
    (x : ParabolicSpace) :
    ((Finset.Icc ⌈(4 : ℝ) ^ (n + 1) * (x.1 - (lam + 8 * ((2 : ℝ) ^ (n + 1))⁻¹) ^ 2)⌉
        ⌊(4 : ℝ) ^ (n + 1) * (x.1 + (lam + 8 * ((2 : ℝ) ^ (n + 1))⁻¹) ^ 2)⌋).card : ℝ) ≤
      11 * (lam * 2 ^ n) ^ 2 := by
  have h := card_latticeBox_time_le (n + 1) x (rt := (lam + 8 * ((2 : ℝ) ^ (n + 1))⁻¹) ^ 2)
    (by positivity)
  refine h.trans ?_
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (n + 1) := by positivity
  have e : 2 * (4 : ℝ) ^ (n + 1) * (lam + 8 * ((2 : ℝ) ^ (n + 1))⁻¹) ^ 2 =
      2 * (2 * (lam * 2 ^ n) + 8) ^ 2 := by
    rw [four_pow, pow_succ]; field_simp; ring
  rw [e]
  nlinarith

theorem card_latticeBox_space_succ_le {n : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (hΛ : 32 ≤ lam * 2 ^ n) (x : ParabolicSpace) :
    ((Fintype.piFinset fun i : Fin 3 =>
      Finset.Icc ⌈(2 : ℝ) ^ (n + 1) * (x.2 i - (lam + 8 * ((2 : ℝ) ^ (n + 1))⁻¹))⌉
        ⌊(2 : ℝ) ^ (n + 1) * (x.2 i + (lam + 8 * ((2 : ℝ) ^ (n + 1))⁻¹))⌋).card : ℝ) ≤
      125 * (lam * 2 ^ n) ^ 3 := by
  have h := card_latticeBox_space_le (n + 1) x (rs := lam + 8 * ((2 : ℝ) ^ (n + 1))⁻¹)
    (by positivity)
  refine h.trans ?_
  have := two_mul_succ_le hΛ
  have h0 : 0 ≤ 2 * (2 : ℝ) ^ (n + 1) * (lam + 8 * ((2 : ℝ) ^ (n + 1))⁻¹) + 2 := by positivity
  calc _ ≤ (5 * (lam * 2 ^ n)) ^ 3 := pow_le_pow_left₀ h0 this 3
    _ = _ := by ring

theorem card_latticeBox_near_succ_le {n : ℕ} {lam : ℝ} (hlam : 0 < lam) (hΛ : 32 ≤ lam * 2 ^ n)
    (ξ : ParabolicSpace) :
    ((latticeBox (n + 1) ξ (216 * (((2 : ℝ) ^ n)⁻¹) ^ 2)
      (lam + 8 * ((2 : ℝ) ^ (n + 1))⁻¹)).card : ℝ) ≤ 1730 * (125 * (lam * 2 ^ n) ^ 3) := by
  have h := card_latticeBox_le (n := n + 1) (x := ξ) (rt := 216 * (((2 : ℝ) ^ n)⁻¹) ^ 2)
    (rs := lam + 8 * ((2 : ℝ) ^ (n + 1))⁻¹) (by positivity) (by positivity)
  refine h.trans ?_
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have e : 2 * (4 : ℝ) ^ (n + 1) * (216 * (((2 : ℝ) ^ n)⁻¹) ^ 2) + 2 = 1730 := by
    rw [four_pow, pow_succ]; field_simp; ring
  rw [e]
  have := two_mul_succ_le hΛ
  have h0 : 0 ≤ 2 * (2 : ℝ) ^ (n + 1) * (lam + 8 * ((2 : ℝ) ^ (n + 1))⁻¹) + 2 := by positivity
  calc 1730 * (2 * (2 : ℝ) ^ (n + 1) * (lam + 8 * ((2 : ℝ) ^ (n + 1))⁻¹) + 2) ^ 3
      ≤ 1730 * (5 * (lam * 2 ^ n)) ^ 3 := by gcongr
    _ = _ := by ring

end RegularityStructures.Layer

end
