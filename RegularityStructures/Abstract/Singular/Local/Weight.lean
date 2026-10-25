/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.WeightedSingularDefs
public import RegularityStructures.Abstract.FixedPointTimeSlab

/-!
# The singular weight of the time slab is 1-Lipschitz

For `ρ = timeZeroDist` (`ρ z = |z₀|^{1/2}`), the weight `w = singularWeight ρ = 1 ∧ ρ` satisfies
`|w z - w z'| ≤ ‖z - z'‖_𝔰`. Consequently, near a point `x` of the slab at distance
`≤ 2 λ ≤ w(x)/32`, the weight is comparable to `w(x)` and positive, and the time coordinate stays
positive. These are the geometric inputs for the local reconstruction bounds
(Hairer, arXiv:1303.5113v4, proof of Prop. 7.2).
-/

public section

namespace RegularityStructures

theorem abs_sqrt_abs_sub_sqrt_abs_le (a b : ℝ) :
    abs (Real.sqrt |a| - Real.sqrt |b|) ≤ Real.sqrt |a - b| := by
  have h1 := sqrt_abs_add_le (a - b) b
  have h2 := sqrt_abs_add_le (b - a) a
  rw [sub_add_cancel] at h1
  rw [sub_add_cancel, abs_sub_comm] at h2
  rw [abs_le]
  constructor <;> linarith

theorem abs_singularWeight_timeZeroDist_sub_le (z z' : ParabolicSpace) :
    |singularWeight timeZeroDist z - singularWeight timeZeroDist z'| ≤ parabolicNorm (z - z') := by
  have h1 : abs (timeZeroDist z - timeZeroDist z') ≤ parabolicNorm (z - z') := by
    refine (abs_sqrt_abs_sub_sqrt_abs_le z.1 z'.1).trans ?_
    unfold parabolicNorm
    simp only [Prod.fst_sub]
    linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => abs_nonneg ((z - z').2 i)]
  have h2 := abs_min_sub_min_le_max 1 (timeZeroDist z) 1 (timeZeroDist z')
  rw [sub_self, abs_zero] at h2
  have h3 : max 0 |timeZeroDist z - timeZeroDist z'| = |timeZeroDist z - timeZeroDist z'| :=
    max_eq_right (abs_nonneg _)
  rw [h3] at h2
  exact h2.trans h1

theorem singularWeight_timeZeroDist_le (z : ParabolicSpace) :
    singularWeight timeZeroDist z ≤ timeZeroDist z :=
  min_le_right _ _

/-- Near a point `x` of the slab with `64 λ ≤ w(x)`, at parabolic distance at most `2 λ`: the
weight is comparable to `w(x)` and the time coordinate is positive. -/
theorem weight_comparable_of_near {x z : ParabolicSpace} {lam : ℝ} (hlam : 0 < lam)
    (hx1 : 0 < x.1) (hx : 64 * lam ≤ singularWeight timeZeroDist x)
    (hz : parabolicNorm (z - x) ≤ 2 * lam) :
    singularWeight timeZeroDist x / 2 ≤ singularWeight timeZeroDist z ∧
      singularWeight timeZeroDist z ≤ 2 * singularWeight timeZeroDist x ∧ 0 < z.1 := by
  have h := abs_singularWeight_timeZeroDist_sub_le z x
  rw [abs_le] at h
  refine ⟨by linarith [h.1, h.2], by linarith [h.1, h.2], ?_⟩
  have hρ : 64 * lam ≤ Real.sqrt x.1 := by
    have : singularWeight timeZeroDist x ≤ Real.sqrt |x.1| := singularWeight_timeZeroDist_le x
    rw [abs_of_pos hx1] at this
    linarith
  have hx2 : (64 * lam) ^ 2 ≤ x.1 := by
    have := pow_le_pow_left₀ (by positivity) hρ 2
    rwa [Real.sq_sqrt hx1.le] at this
  have hd : |z.1 - x.1| ≤ (2 * lam) ^ 2 := by
    have h3 : Real.sqrt |(z - x).1| ≤ 2 * lam := by
      refine le_trans ?_ hz
      unfold parabolicNorm
      linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => abs_nonneg ((z - x).2 i)]
    have := (Real.sqrt_le_left (by positivity)).1 h3
    simpa using this
  rw [abs_le] at hd
  nlinarith [hd.1]

end RegularityStructures

end
