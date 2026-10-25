/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalKernelHairer
import Mathlib.Algebra.Order.Field.GeomSum
public import RegularityStructures.Analysis.Heat.Annihilating.Scaled

/-!
# The dyadic singular bound for Hairer's truncated kernel

This is the pointwise part of the kernel input used in the comparison of the constants in Section 7
of the statement.  The annihilating shells are compactly supported at scale `2⁻ⁿ`; their smooth base
profile is bounded, so the finite shell sum at a nonzero point is bounded by a geometric series of
order `-3`.

The value at the origin is intentionally excluded.  The singular kernel is only used under
Lebesgue integration there, and the `tsum` convention at the origin is irrelevant to all such
statements.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures

namespace Phi43

private theorem exists_abs_annKernel0_le (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : ParabolicSpace, |annKernel0C N z| ≤ B := by
  have hsupport : HasCompactSupport (annKernel0C N) :=
    HasCompactSupport.intro (isCompact_parabolicNorm_le 1) fun z hz =>
      annKernel0C_eq_zero N (not_le.1 hz)
  obtain ⟨B, hB⟩ := (contDiff_annKernel0C N).continuous.abs.bounded_above_of_compact_support
    (hsupport.norm)
  refine ⟨max B 0, le_max_right B 0, ?_⟩
  intro z
  have hz := (hB z).trans (le_max_left B 0)
  simpa only [Real.norm_eq_abs, abs_abs] using hz

private theorem geom_sum_eight_le (M : ℕ) :
    (∑ n ∈ Finset.range M, (8 : ℝ) ^ n) ≤ 2 * (8 : ℝ) ^ M := by
  calc
    (∑ n ∈ Finset.range M, (8 : ℝ) ^ n) =
        ((8 : ℝ) ^ M - 1) / (8 - 1) :=
      by simpa only using
        (geom_sum_eq (x := (8 : ℝ)) (n := M) (by norm_num))
    _ ≤ 2 * (8 : ℝ) ^ M := by
      have hpow : 0 ≤ (8 : ℝ) ^ M := by positivity
      rw [show (8 : ℝ) - 1 = 7 by norm_num]
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 7)).2
      nlinarith

private theorem annShell_abs_le (N n : ℕ) {B : ℝ}
    (hB : ∀ z : ParabolicSpace, |annKernel0C N z| ≤ B) (z : ParabolicSpace) :
    |annShellC N n z| ≤ B * (8 : ℝ) ^ n := by
  have hscale : 0 ≤ (2 : ℝ) ^ n := by positivity
  rw [annShellC, scaledShell, abs_mul, abs_of_nonneg (by positivity)]
  calc
    (2 ^ n) ^ 3 * |annKernel0C N (parabolicDilate (2 ^ n) z)| ≤
        (2 ^ n) ^ 3 * B := mul_le_mul_of_nonneg_left (hB _) (by positivity)
    _ = B * (8 : ℝ) ^ n := by
      rw [show ((2 : ℝ) ^ n) ^ 3 = (2 ^ 3 : ℝ) ^ n by
        calc
          ((2 : ℝ) ^ n) ^ 3 = (2 : ℝ) ^ (n * 3) := (pow_mul (2 : ℝ) n 3).symm
          _ = (2 : ℝ) ^ (3 * n) := by rw [Nat.mul_comm]
          _ = ((2 : ℝ) ^ 3) ^ n := pow_mul (2 : ℝ) 3 n]
      norm_num
      ring

theorem hairerKernel_singular_bound (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {z : ParabolicSpace}, z ≠ 0 →
      |hairerKernel N z| ≤ C * parabolicNorm z ^ (-(3 : ℝ)) := by
  obtain ⟨B, hB, hBase⟩ := exists_abs_annKernel0_le N
  refine ⟨16 * B, by positivity, ?_⟩
  intro z hz
  have hr : 0 < parabolicNorm z :=
    lt_of_lt_of_le (smoothParabolicNorm_pos hz) (smoothParabolicNorm_le_parabolicNorm z)
  obtain ⟨M, hM⟩ := exists_inv_pow_lt hz
  let P : ℕ → Prop := fun m => (2 : ℝ)⁻¹ ^ m < parabolicNorm z
  let m : ℕ := Nat.find (show ∃ m, P m from ⟨M, hM⟩)
  have hm : P m := Nat.find_spec (show ∃ m, P m from ⟨M, hM⟩)
  have hvan : ∀ n, m ≤ n → annShellC N n z = 0 := by
    intro n hmn
    apply annShellC_eq_zero
    have hm' : (2 : ℝ)⁻¹ ^ m < parabolicNorm z := by simpa [P] using hm
    have hpow : (2 : ℝ)⁻¹ ^ n ≤ (2 : ℝ)⁻¹ ^ m :=
      pow_le_pow_of_le_one (a := (2 : ℝ)⁻¹) (by positivity) (by norm_num) hmn
    exact hpow.trans_lt hm'
  have hsum : hairerKernel N z = ∑ n ∈ Finset.range m, annShellC N n z := by
    unfold hairerKernel
    rw [tsum_eq_sum]
    intro n hn
    exact hvan n (not_lt.1 (by simpa using hn))
  have hgeom : (∑ n ∈ Finset.range m, |annShellC N n z|) ≤
      B * (2 * (8 : ℝ) ^ m) := by
    calc
      (∑ n ∈ Finset.range m, |annShellC N n z|) ≤
          ∑ n ∈ Finset.range m, B * (8 : ℝ) ^ n := by
        exact Finset.sum_le_sum fun n hn => annShell_abs_le N n hBase z
      _ = B * (∑ n ∈ Finset.range m, (8 : ℝ) ^ n) := by
        rw [Finset.mul_sum]
      _ ≤ B * (2 * (8 : ℝ) ^ m) := by
        exact mul_le_mul_of_nonneg_left (geom_sum_eight_le m) hB
  have hsum_abs : |hairerKernel N z| ≤
      ∑ n ∈ Finset.range m, |annShellC N n z| := by
    rw [hsum]
    simpa only [Real.norm_eq_abs] using
      (norm_sum_le (Finset.range m) (fun n => annShellC N n z))
  by_cases hm0 : m = 0
  · rw [hsum]
    simp [hm0]
    positivity
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    have hscale : (8 : ℝ) ^ m ≤ 8 * parabolicNorm z ^ (-(3 : ℝ)) := by
      have hprevnot : ¬ P (m - 1) := by
        intro hp
        have hle : m ≤ m - 1 := by
          simpa [m] using Nat.find_min' (show ∃ m, P m from ⟨M, hM⟩) hp
        omega
      have hprev : parabolicNorm z ≤ (2 : ℝ)⁻¹ ^ (m - 1) :=
        le_of_not_gt hprevnot
      have hmul : parabolicNorm z * (2 : ℝ) ^ m ≤ 2 := by
        have hpow : (2 : ℝ)⁻¹ ^ (m - 1) * (2 : ℝ) ^ m = 2 := by
          have heq : (2 : ℝ) ^ m = (2 : ℝ) ^ (m - 1) * 2 := by
            calc
              (2 : ℝ) ^ m = (2 : ℝ) ^ ((m - 1) + 1) := by
                congr 1
                omega
              _ = (2 : ℝ) ^ (m - 1) * (2 : ℝ) ^ 1 := pow_add _ _ _
              _ = (2 : ℝ) ^ (m - 1) * 2 := by norm_num
          calc
            (2 : ℝ)⁻¹ ^ (m - 1) * (2 : ℝ) ^ m =
                (2 ^ (m - 1))⁻¹ * (2 ^ (m - 1) * 2) := by
                  rw [inv_pow, heq]
            _ = 2 := by
              rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
        calc
          parabolicNorm z * (2 : ℝ) ^ m ≤
              ((2 : ℝ)⁻¹ ^ (m - 1)) * (2 : ℝ) ^ m :=
            mul_le_mul_of_nonneg_right hprev (by positivity)
          _ = 2 := hpow
      have hpowle : (2 : ℝ) ^ m ≤ 2 / parabolicNorm z := by
        exact (le_div_iff₀ hr).2 (by simpa [mul_comm] using hmul)
      have hpowle3 : ((2 : ℝ) ^ m) ^ 3 ≤ (2 / parabolicNorm z) ^ 3 := by
        exact pow_le_pow_left₀ (by positivity) hpowle 3
      calc
        (8 : ℝ) ^ m = ((2 : ℝ) ^ 3) ^ m := by norm_num
        _ = ((2 : ℝ) ^ m) ^ 3 := by
          calc
            ((2 : ℝ) ^ 3) ^ m = (2 : ℝ) ^ (3 * m) := (pow_mul (2 : ℝ) 3 m).symm
            _ = (2 : ℝ) ^ (m * 3) := by rw [Nat.mul_comm]
            _ = ((2 : ℝ) ^ m) ^ 3 := pow_mul (2 : ℝ) m 3
        _ ≤ (2 / parabolicNorm z) ^ 3 := hpowle3
        _ = 8 * parabolicNorm z ^ (-(3 : ℝ)) := by
          rw [Real.rpow_neg (le_of_lt hr)]
          field_simp
          norm_num
          ring
    calc
      |hairerKernel N z| ≤ B * (2 * (8 : ℝ) ^ m) := hsum_abs.trans hgeom
      _ = (2 * B) * (8 : ℝ) ^ m := by ring
      _ ≤ (2 * B) * (8 * parabolicNorm z ^ (-(3 : ℝ))) :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = (16 * B) * parabolicNorm z ^ (-(3 : ℝ)) := by ring

end Phi43

end RegularityStructures

end
