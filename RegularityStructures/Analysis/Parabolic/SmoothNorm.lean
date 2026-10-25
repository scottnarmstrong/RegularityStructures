/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.Basic
public import RegularityStructures.Torus.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A smooth parabolic norm on `ℝ⁴`

`smoothParabolicNorm z = (z₀² + |z'|⁴)^{1/4}` is smooth away from `0`, `1`-homogeneous for the
parabolic dilation, and comparable to `parabolicNorm`. It is the smooth parabolic norm `N` used to
cut homogeneous kernels into dyadic shells in [Hai14, Lemma 5.5] (arXiv:1303.5113v4).
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- A smooth (away from `0`) parabolic norm `(z₀² + |z'|⁴)^{1/4}`, where `|z'|² = sqNorm3 z'`. -/
def smoothParabolicNorm (z : ParabolicSpace) : ℝ := (z.1 ^ 2 + sqNorm3 z.2 ^ 2) ^ (1 / 4 : ℝ)

end RegularityStructures

end

public section

namespace RegularityStructures

theorem sqNorm3_nonneg (v : Fin 3 → ℝ) : 0 ≤ sqNorm3 v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem sqNorm3_smul (c : ℝ) (v : Fin 3 → ℝ) : sqNorm3 (c • v) = c ^ 2 * sqNorm3 v := by
  simp [sqNorm3, mul_pow, Finset.mul_sum]

theorem sqNorm3_eq_zero_iff (v : Fin 3 → ℝ) : sqNorm3 v = 0 ↔ v = 0 := by
  unfold sqNorm3
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)]
  simp [funext_iff]

theorem smoothParabolicNorm_inner_nonneg (z : ParabolicSpace) :
    0 ≤ z.1 ^ 2 + sqNorm3 z.2 ^ 2 := by
  have := sq_nonneg z.1
  have := sq_nonneg (sqNorm3 z.2)
  linarith

theorem smoothParabolicNorm_nonneg (z : ParabolicSpace) : 0 ≤ smoothParabolicNorm z :=
  Real.rpow_nonneg (smoothParabolicNorm_inner_nonneg z) _

theorem smoothParabolicNorm_pow_four (z : ParabolicSpace) :
    smoothParabolicNorm z ^ 4 = z.1 ^ 2 + sqNorm3 z.2 ^ 2 := by
  unfold smoothParabolicNorm
  rw [← Real.rpow_natCast, ← Real.rpow_mul (smoothParabolicNorm_inner_nonneg z)]
  norm_num

theorem smoothParabolicNorm_eq_zero_iff {z : ParabolicSpace} :
    smoothParabolicNorm z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have h4 := smoothParabolicNorm_pow_four z
    rw [h] at h4
    have h1 := sq_nonneg z.1
    have h2 := sq_nonneg (sqNorm3 z.2)
    have ht : z.1 = 0 := by nlinarith
    have hs : sqNorm3 z.2 = 0 := by nlinarith
    exact Prod.ext ht ((sqNorm3_eq_zero_iff _).1 hs)
  · rintro rfl
    simp [smoothParabolicNorm, sqNorm3]

theorem smoothParabolicNorm_pos {z : ParabolicSpace} (hz : z ≠ 0) : 0 < smoothParabolicNorm z :=
  lt_of_le_of_ne (smoothParabolicNorm_nonneg z)
    (fun h => hz (smoothParabolicNorm_eq_zero_iff.1 h.symm))

theorem continuous_smoothParabolicNorm : Continuous smoothParabolicNorm := by
  have : Continuous fun z : ParabolicSpace => z.1 ^ 2 + sqNorm3 z.2 ^ 2 := by
    unfold sqNorm3
    fun_prop
  exact this.rpow_const fun z => Or.inr (by norm_num)

theorem smoothParabolicNorm_parabolicDilate {c : ℝ} (hc : 0 ≤ c) (z : ParabolicSpace) :
    smoothParabolicNorm (parabolicDilate c z) = c * smoothParabolicNorm z := by
  have h4 : smoothParabolicNorm (parabolicDilate c z) ^ 4 = (c * smoothParabolicNorm z) ^ 4 := by
    rw [smoothParabolicNorm_pow_four, mul_pow, smoothParabolicNorm_pow_four]
    simp only [parabolicDilate, sqNorm3_smul]
    ring
  exact (pow_left_inj₀ (smoothParabolicNorm_nonneg _)
    (mul_nonneg hc (smoothParabolicNorm_nonneg _)) (by norm_num)).1 h4

open scoped ContDiff in
theorem contDiffAt_smoothParabolicNorm {z : ParabolicSpace} (hz : z ≠ 0) :
    ContDiffAt ℝ ∞ smoothParabolicNorm z := by
  have hp : ContDiff ℝ ∞ fun z : ParabolicSpace => z.1 ^ 2 + sqNorm3 z.2 ^ 2 := by
    unfold sqNorm3
    fun_prop
  refine hp.contDiffAt.rpow_const_of_ne ?_
  have h4 := smoothParabolicNorm_pow_four z
  have hpos := pow_pos (smoothParabolicNorm_pos hz) 4
  intro h0
  rw [h4] at hpos
  exact hpos.ne' h0

theorem parabolicNorm_le_four_mul_smoothParabolicNorm (z : ParabolicSpace) :
    parabolicNorm z ≤ 4 * smoothParabolicNorm z := by
  have hN := smoothParabolicNorm_nonneg z
  have h4 := smoothParabolicNorm_pow_four z
  have hs := sqNorm3_nonneg z.2
  have hx : ∀ i, |z.2 i| ≤ smoothParabolicNorm z := by
    intro i
    refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) hN ?_
    rw [h4]
    have hi : z.2 i ^ 2 ≤ sqNorm3 z.2 := by
      unfold sqNorm3
      exact Finset.single_le_sum (f := fun j => z.2 j ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ i)
    have : |z.2 i| ^ 4 = (z.2 i ^ 2) ^ 2 := by
      rw [← sq_abs (z.2 i)]; ring
    rw [this]
    nlinarith [sq_nonneg z.1, sq_nonneg (z.2 i ^ 2), sq_nonneg (z.2 i)]
  have ht : Real.sqrt |z.1| ≤ smoothParabolicNorm z := by
    refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) hN ?_
    rw [h4]
    have : Real.sqrt |z.1| ^ 4 = z.1 ^ 2 := by
      have := Real.sq_sqrt (abs_nonneg z.1)
      calc Real.sqrt |z.1| ^ 4 = (Real.sqrt |z.1| ^ 2) ^ 2 := by ring
        _ = z.1 ^ 2 := by rw [this, sq_abs]
    rw [this]
    nlinarith [sq_nonneg (sqNorm3 z.2)]
  unfold parabolicNorm
  simp only [Fin.sum_univ_three] at *
  linarith [hx 0, hx 1, hx 2]

theorem smoothParabolicNorm_le_parabolicNorm (z : ParabolicSpace) :
    smoothParabolicNorm z ≤ parabolicNorm z := by
  have hN := smoothParabolicNorm_nonneg z
  have hp := parabolicNorm_nonneg z
  refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) hp ?_
  rw [smoothParabolicNorm_pow_four]
  set a := Real.sqrt |z.1| with ha
  set b := ∑ i, |z.2 i| with hb
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have ha4 : a ^ 4 = z.1 ^ 2 := by
    have := Real.sq_sqrt (abs_nonneg z.1)
    calc a ^ 4 = (a ^ 2) ^ 2 := by ring
      _ = z.1 ^ 2 := by rw [ha, this, sq_abs]
  have hsb : sqNorm3 z.2 ≤ b ^ 2 := by
    simp only [sqNorm3, hb, Fin.sum_univ_three]
    have h0 := abs_nonneg (z.2 0)
    have h1 := abs_nonneg (z.2 1)
    have h2 := abs_nonneg (z.2 2)
    rw [← sq_abs (z.2 0), ← sq_abs (z.2 1), ← sq_abs (z.2 2)]
    nlinarith [mul_nonneg h0 h1, mul_nonneg h0 h2, mul_nonneg h1 h2]
  have hs0 := sqNorm3_nonneg z.2
  have hsb2 : sqNorm3 z.2 ^ 2 ≤ b ^ 4 := by
    calc sqNorm3 z.2 ^ 2 ≤ (b ^ 2) ^ 2 := pow_le_pow_left₀ hs0 hsb 2
      _ = b ^ 4 := by ring
  show z.1 ^ 2 + sqNorm3 z.2 ^ 2 ≤ (parabolicNorm z) ^ 4
  have : parabolicNorm z = a + b := rfl
  rw [this, ← ha4]
  nlinarith [mul_nonneg ha0 hb0, pow_nonneg ha0 3, pow_nonneg hb0 3, pow_nonneg ha0 2,
    pow_nonneg hb0 2, mul_nonneg (pow_nonneg ha0 2) (pow_nonneg hb0 2),
    mul_nonneg (pow_nonneg ha0 3) hb0, mul_nonneg ha0 (pow_nonneg hb0 3)]

end RegularityStructures

end
