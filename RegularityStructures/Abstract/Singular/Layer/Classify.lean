/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Layer.Geometry
public import RegularityStructures.Analysis.Parabolic.Lattice.Cell

/-!
# Geometry of a pair of overlapping lattice cells

Pure geometric facts about a pair `(z', z) = (z_{n+1,k}, z_{n,l})` of lattice points whose cells
overlap, `r = 2^{-n}`:

* `d(z', z) ≤ 12 r` and `|z'_0 - z_0| ≤ 144 r²`, both points have time below the common point;
* a pair that is not "regular" (both times positive and `d ≤ min (w z') (w z)`) but has a point of
  positive time has `z'_0 ∈ (-144 r², 288 r²]` when `r ≤ 1/32`;
* the weight comparison `W^e ≤ 2^θ (1 + u^{-θ})` for `W ∈ [w/2, w]`, `w = min 1 u`.
-/

public section

namespace RegularityStructures.Layer

theorem abs_snd_sub_le (y x : ParabolicSpace) (i : Fin 3) :
    |y.2 i - x.2 i| ≤ parabolicNorm (y - x) := by
  unfold parabolicNorm
  have h1 : |y.2 i - x.2 i| ≤ ∑ j, |y.2 j - x.2 j| :=
    Finset.single_le_sum (f := fun j => |y.2 j - x.2 j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)
  have h2 := Real.sqrt_nonneg |y.1 - x.1|
  simp only [Prod.fst_sub, Prod.snd_sub, Pi.sub_apply]
  linarith

/-- Geometry of two overlapping cells at a common point `w`. -/
theorem pair_geometry {n : ℕ} {k l : LatticeIndex} {w : ParabolicSpace}
    (h1 : latticeCell (n + 1) k w ≠ 0) (h2 : latticeCell n l w ≠ 0) :
    parabolicNorm (w - latticePoint (n + 1) k) ≤ 4 * ((2 : ℝ) ^ n)⁻¹ ∧
    parabolicNorm (w - latticePoint n l) ≤ 8 * ((2 : ℝ) ^ n)⁻¹ ∧
    (latticePoint (n + 1) k).1 < w.1 ∧ (latticePoint n l).1 < w.1 ∧
    parabolicNorm (latticePoint (n + 1) k - latticePoint n l) ≤ 12 * ((2 : ℝ) ^ n)⁻¹ := by
  have e : 8 * ((2 : ℝ) ^ (n + 1))⁻¹ = 4 * ((2 : ℝ) ^ n)⁻¹ := by
    rw [pow_succ, mul_inv]; ring
  have a1 := parabolicNorm_sub_latticePoint_le h1
  have a2 := parabolicNorm_sub_latticePoint_le h2
  rw [e] at a1
  have c1 := (latticeCell_ne_zero h1).1.1
  have c2 := (latticeCell_ne_zero h2).1.1
  refine ⟨a1, a2, by linarith, by linarith, ?_⟩
  have e2 : latticePoint (n + 1) k - latticePoint n l =
      (latticePoint (n + 1) k - w) + (w - latticePoint n l) := by abel
  rw [e2]
  refine (parabolicNorm_add_le _ _).trans ?_
  rw [parabolicNorm_sub_comm (latticePoint (n + 1) k) w]
  linarith

/-- Time window of a pair that is not regular. -/
theorem near_time_bounds {z' z : ParabolicSpace} {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 32)
    (hd : parabolicNorm (z' - z) ≤ 12 * r)
    (hnr : ¬(0 < z'.1 ∧ 0 < z.1 ∧ parabolicNorm (z' - z) ≤
      min (singularWeight timeZeroDist z') (singularWeight timeZeroDist z)))
    (hpos : 0 < z'.1 ∨ 0 < z.1) : -(144 * r ^ 2) < z'.1 ∧ z'.1 ≤ 288 * r ^ 2 := by
  have hd0 := parabolicNorm_nonneg (z' - z)
  have hab := abs_fst_sub_le_sq z' z
  have hd2 : parabolicNorm (z' - z) ^ 2 ≤ 144 * r ^ 2 := by nlinarith
  have hab' := abs_le.1 (hab.trans hd2)
  by_cases ha : 0 < z'.1
  · by_cases hb : 0 < z.1
    · have hW : min (singularWeight timeZeroDist z') (singularWeight timeZeroDist z) <
          parabolicNorm (z' - z) := by
        by_contra hc; exact hnr ⟨ha, hb, not_lt.1 hc⟩
      have hd1 : parabolicNorm (z' - z) < 1 := by linarith
      rcases min_lt_iff.1 hW with h | h
      · have h' : timeZeroDist z' < parabolicNorm (z' - z) := by
          unfold singularWeight at h
          rcases min_lt_iff.1 h with h | h
          · linarith
          · exact h
        have : z'.1 < parabolicNorm (z' - z) ^ 2 := by
          unfold timeZeroDist at h'
          rw [abs_of_pos ha] at h'
          exact (Real.sqrt_lt' (lt_of_le_of_lt (Real.sqrt_nonneg _) h')).1 h'
        exact ⟨by linarith, by linarith⟩
      · have h' : timeZeroDist z < parabolicNorm (z' - z) := by
          unfold singularWeight at h
          rcases min_lt_iff.1 h with h | h
          · linarith
          · exact h
        have : z.1 < parabolicNorm (z' - z) ^ 2 := by
          unfold timeZeroDist at h'
          rw [abs_of_pos hb] at h'
          exact (Real.sqrt_lt' (lt_of_le_of_lt (Real.sqrt_nonneg _) h')).1 h'
        exact ⟨by linarith, by linarith⟩
    · push Not at hb
      exact ⟨by linarith, by linarith⟩
  · push Not at ha
    have hb : 0 < z.1 := by
      rcases hpos with h | h
      · exact absurd h (not_lt.2 ha)
      · exact h
    exact ⟨by linarith, by nlinarith⟩

/-- `W^e ≤ 2^θ (1 + u^{-θ})` for `min 1 u / 2 ≤ W ≤ min 1 u`, `θ = max (-e) 0`. -/
theorem rpow_le_of_half_le {u W : ℝ} (e : ℝ) (hu : 0 < u) (hW1 : min 1 u / 2 ≤ W)
    (hW2 : W ≤ min 1 u) :
    W ^ e ≤ (2 : ℝ) ^ (max (-e) 0) * (1 + u ^ (-(max (-e) 0))) := by
  have hm : 0 < min 1 u := lt_min one_pos hu
  have hWp : 0 < W := lt_of_lt_of_le (by positivity) hW1
  rcases le_or_gt 0 e with he | he
  · have h1 : W ^ e ≤ 1 :=
      Real.rpow_le_one hWp.le (hW2.trans (min_le_left _ _)) he
    rw [max_eq_right (by linarith : -e ≤ 0)]
    simp only [neg_zero, Real.rpow_zero]
    linarith
  · rw [max_eq_left (by linarith : 0 ≤ -e), neg_neg]
    have h1 : W ^ e ≤ (min 1 u / 2) ^ e :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hW1 he.le
    have h2 : (min 1 u / 2) ^ e = (min 1 u) ^ e * (2 : ℝ) ^ (-e) := by
      rw [Real.div_rpow hm.le (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num)]
    have h3 : (min 1 u) ^ e ≤ 1 + u ^ e := by
      have hue : 0 ≤ u ^ e := Real.rpow_nonneg hu.le _
      rcases le_total 1 u with h | h
      · rw [min_eq_left h, Real.one_rpow]; linarith
      · rw [min_eq_right h]; linarith
    calc W ^ e ≤ (min 1 u) ^ e * (2 : ℝ) ^ (-e) := h2 ▸ h1
      _ ≤ (1 + u ^ e) * (2 : ℝ) ^ (-e) :=
          mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg (by norm_num) _)
      _ = _ := by ring

end RegularityStructures.Layer

end
