/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Kernel.GeneratorLimit

/-!
# Parabolic Lipschitz bound for compactly supported smooth functions

`|φ(y) - φ(z)| ≤ C ‖y - z‖_𝔰`: for `|y₀ - z₀| ≤ 1` the sup norm is dominated by `‖·‖_𝔰` and `φ`
is Lipschitz; otherwise `‖y - z‖_𝔰 ≥ 1` and `φ` is bounded.
-/

public section

open scoped ContDiff

namespace RegularityStructures

theorem norm_le_parabolicNorm {w : ParabolicSpace} (hw : |w.1| ≤ 1) : ‖w‖ ≤ parabolicNorm w := by
  have h1 : |w.1| ≤ Real.sqrt |w.1| := by
    have h0 : 0 ≤ |w.1| := abs_nonneg _
    have := Real.sqrt_le_sqrt hw
    rw [Real.sqrt_one] at this
    calc |w.1| = Real.sqrt |w.1| * Real.sqrt |w.1| := (Real.mul_self_sqrt h0).symm
      _ ≤ Real.sqrt |w.1| * 1 := mul_le_mul_of_nonneg_left this (Real.sqrt_nonneg _)
      _ = _ := mul_one _
  have h2 : ‖w.2‖ ≤ ∑ i, |w.2 i| := by
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)).2 fun i => ?_
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (f := fun i => |w.2 i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
  have h3 : 0 ≤ ∑ i, |w.2 i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have h4 := Real.sqrt_nonneg |w.1|
  rw [Prod.norm_def, Real.norm_eq_abs]
  unfold parabolicNorm
  exact max_le (by linarith) (by linarith)

theorem one_le_parabolicNorm {w : ParabolicSpace} (hw : 1 < |w.1|) : 1 ≤ parabolicNorm w := by
  have h1 : 1 ≤ Real.sqrt |w.1| := by
    exact Real.le_sqrt_of_sq_le (by nlinarith [abs_nonneg w.1])
  have h3 : 0 ≤ ∑ i, |w.2 i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  unfold parabolicNorm
  linarith

theorem exists_abs_sub_le_parabolicNorm {φ : ParabolicSpace → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y z, |φ y - φ z| ≤ C * parabolicNorm (y - z) := by
  obtain ⟨L, hL⟩ := hφ.lipschitzWith_of_hasCompactSupport hc (by simp)
  obtain ⟨B, hB⟩ := hφ.continuous.bounded_above_of_compact_support hc
  refine ⟨L + 2 * max B 0, add_nonneg L.coe_nonneg (mul_nonneg (by norm_num) (le_max_right _ _)),
    fun y z => ?_⟩
  have hLd : |φ y - φ z| ≤ L * ‖y - z‖ := by
    have := hL.dist_le_mul y z
    rwa [Real.dist_eq, dist_eq_norm] at this
  have hbd : |φ y - φ z| ≤ 2 * max B 0 := by
    have h1 := hB y
    have h2 := hB z
    rw [Real.norm_eq_abs] at h1 h2
    have h3 : B ≤ max B 0 := le_max_left _ _
    calc |φ y - φ z| ≤ |φ y| + |φ z| := abs_sub _ _
      _ ≤ 2 * max B 0 := by linarith
  have hpn := parabolicNorm_nonneg (y - z)
  have hL0 : (0 : ℝ) ≤ L := L.coe_nonneg
  have hM : 0 ≤ max B 0 := le_max_right _ _
  rcases le_or_gt |(y - z).1| 1 with h | h
  · have := norm_le_parabolicNorm h
    calc |φ y - φ z| ≤ L * ‖y - z‖ := hLd
      _ ≤ L * parabolicNorm (y - z) := mul_le_mul_of_nonneg_left this hL0
      _ ≤ (L + 2 * max B 0) * parabolicNorm (y - z) :=
        mul_le_mul_of_nonneg_right (by linarith) hpn
  · have := one_le_parabolicNorm h
    calc |φ y - φ z| ≤ 2 * max B 0 := hbd
      _ ≤ 2 * max B 0 * parabolicNorm (y - z) := by nlinarith
      _ ≤ (L + 2 * max B 0) * parabolicNorm (y - z) :=
        mul_le_mul_of_nonneg_right (by linarith) hpn

end RegularityStructures

end
