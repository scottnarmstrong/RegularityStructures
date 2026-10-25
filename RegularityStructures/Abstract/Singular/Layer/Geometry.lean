/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.WeightedSingularDefs
public import RegularityStructures.Abstract.FixedPointTimeSlab
public import RegularityStructures.Analysis.Parabolic.Lattice.Cell

/-!
# Elementary geometry for the layer bound

Lipschitz continuity of the weight `singularWeight timeZeroDist`, lower bounds for the weight at
lattice points of positive time, time differences controlled by the parabolic size, and the choice
of the first lattice level `n₀` with `32 < λ 2^{n₀} ≤ 64`.
-/

public section

namespace RegularityStructures.Layer

theorem abs_sqrt_sub_sqrt_le_sqrt_abs_sub (a b : ℝ) : abs (Real.sqrt |a| - Real.sqrt |b|) ≤ Real.sqrt |a - b| := by
  rw [abs_le]
  constructor
  · have := sqrt_abs_add_le (b - a) a
    rw [sub_add_cancel, ← abs_neg (b - a), neg_sub] at this
    linarith
  · have := sqrt_abs_add_le (a - b) b
    rw [sub_add_cancel] at this
    linarith

theorem sqrt_abs_fst_sub_le (y x : ParabolicSpace) : Real.sqrt |y.1 - x.1| ≤ parabolicNorm (y - x) := by
  unfold parabolicNorm
  simp only [Prod.fst_sub]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)

theorem abs_fst_sub_le_sq (y x : ParabolicSpace) : |y.1 - x.1| ≤ parabolicNorm (y - x) ^ 2 := by
  have h := sqrt_abs_fst_sub_le y x
  have h0 : 0 ≤ Real.sqrt |y.1 - x.1| := Real.sqrt_nonneg _
  calc |y.1 - x.1| = (Real.sqrt |y.1 - x.1|) ^ 2 := (Real.sq_sqrt (abs_nonneg _)).symm
    _ ≤ _ := pow_le_pow_left₀ h0 h 2

theorem abs_timeZeroDist_sub_le (y x : ParabolicSpace) :
    |timeZeroDist y - timeZeroDist x| ≤ parabolicNorm (y - x) :=
  (abs_sqrt_sub_sqrt_le_sqrt_abs_sub y.1 x.1).trans (sqrt_abs_fst_sub_le y x)

theorem abs_singularWeight_sub_le (y x : ParabolicSpace) :
    |singularWeight timeZeroDist y - singularWeight timeZeroDist x| ≤ parabolicNorm (y - x) := by
  unfold singularWeight
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  simp only [sub_self, abs_zero, max_le_iff]
  exact ⟨parabolicNorm_nonneg _, abs_timeZeroDist_sub_le y x⟩

theorem singularWeight_nonneg (y : ParabolicSpace) : 0 ≤ singularWeight timeZeroDist y :=
  le_min zero_le_one (Real.sqrt_nonneg _)

/-- If `d(y, x) ≤ min (w y) (w x)` then `min (w y) (w x) ≥ w y / 2`. -/
theorem half_singularWeight_le_min {y x : ParabolicSpace}
    (h : parabolicNorm (y - x) ≤ min (singularWeight timeZeroDist y)
      (singularWeight timeZeroDist x)) :
    singularWeight timeZeroDist y / 2 ≤
      min (singularWeight timeZeroDist y) (singularWeight timeZeroDist x) := by
  have h1 := abs_singularWeight_sub_le y x
  have hy := singularWeight_nonneg y
  have hx : parabolicNorm (y - x) ≤ singularWeight timeZeroDist x := h.trans (min_le_right _ _)
  refine le_min (by linarith) ?_
  have := (abs_le.1 h1).2
  linarith

theorem four_pow_inv_le_latticePoint_fst {n : ℕ} {k : LatticeIndex}
    (h : 0 < (latticePoint n k).1) : ((4 : ℝ) ^ n)⁻¹ ≤ (latticePoint n k).1 := by
  rw [latticePoint_fst] at h ⊢
  have hk : (0 : ℝ) < k.1 := pos_of_mul_pos_right h (by positivity)
  have hk1 : (1 : ℝ) ≤ k.1 := by exact_mod_cast (show (1 : ℤ) ≤ k.1 by exact_mod_cast hk)
  have e : (((2 : ℝ) ^ n)⁻¹) ^ 2 = ((4 : ℝ) ^ n)⁻¹ := by
    rw [inv_pow, ← pow_mul, mul_comm, pow_mul]; norm_num
  rw [e]
  exact le_mul_of_one_le_right (by positivity) hk1

theorem inv_two_pow_le_singularWeight {n : ℕ} {k : LatticeIndex} (h : 0 < (latticePoint n k).1) :
    ((2 : ℝ) ^ n)⁻¹ ≤ singularWeight timeZeroDist (latticePoint n k) := by
  have h1 := four_pow_inv_le_latticePoint_fst h
  refine le_min ?_ ?_
  · exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  · unfold timeZeroDist
    refine Real.le_sqrt_of_sq_le ?_
    rw [abs_of_pos h]
    have e : (((2 : ℝ) ^ n)⁻¹) ^ 2 = ((4 : ℝ) ^ n)⁻¹ := by
      rw [inv_pow, ← pow_mul, mul_comm, pow_mul]; norm_num
    rw [e]; exact h1

theorem exists_nat_scale {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) :
    ∃ n₀ : ℕ, 32 < lam * 2 ^ n₀ ∧ lam * 2 ^ n₀ ≤ 64 := by
  have hx : (1 : ℝ) ≤ 32 / lam := by
    rw [le_div_iff₀ h0]; linarith
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 2)
  refine ⟨n + 1, ?_, ?_⟩
  · rw [div_lt_iff₀ h0] at hn2; linarith
  · rw [le_div_iff₀ h0] at hn1; rw [pow_succ]; nlinarith

end RegularityStructures.Layer

end
