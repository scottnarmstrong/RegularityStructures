/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesClean
public import Phi43.BPHZ.TreeI3Psi2DiagramLeaves

/-!
# Comparison of the singular terms with `treeTheta`

For `z, z', z - z'` away from the origin, powers `s^(-e)`, `0 ≤ e ≤ 5/2`, of any of the three
distances are bounded by `treeTheta z z'`; products of two powers with exponents at most `5/4` are
bounded by `2 treeTheta z z'`; and `i3Psi2S η z z' ≤ 3 treeTheta z z'` for `0 ≤ η ≤ 5/2`.
-/

public section

namespace RegularityStructures

section

variable {z z' : SpaceTime}

theorem rpow_zz_le_treeTheta (hzz : 0 < torusParabolicSize (z - z')) {e : ℝ} (he : 0 ≤ e)
    (he' : e ≤ 5 / 2) : torusParabolicSize (z - z') ^ (-e) ≤ treeTheta z z' := by
  have h := rpow_neg_le_five_halves_add_one hzz he he'
  unfold treeTheta
  have := Real.rpow_nonneg (torusParabolicSize_nonneg z) (-(5 / 2 : ℝ))
  have := Real.rpow_nonneg (torusParabolicSize_nonneg z') (-(5 / 2 : ℝ))
  linarith

theorem rpow_z_le_treeTheta (hz : 0 < torusParabolicSize z) {e : ℝ} (he : 0 ≤ e)
    (he' : e ≤ 5 / 2) : torusParabolicSize z ^ (-e) ≤ treeTheta z z' := by
  have h := rpow_neg_le_five_halves_add_one hz he he'
  unfold treeTheta
  have := Real.rpow_nonneg (torusParabolicSize_nonneg (z - z')) (-(5 / 2 : ℝ))
  have := Real.rpow_nonneg (torusParabolicSize_nonneg z') (-(5 / 2 : ℝ))
  linarith

theorem rpow_z'_le_treeTheta (hz' : 0 < torusParabolicSize z') {e : ℝ} (he : 0 ≤ e)
    (he' : e ≤ 5 / 2) : torusParabolicSize z' ^ (-e) ≤ treeTheta z z' := by
  have h := rpow_neg_le_five_halves_add_one hz' he he'
  unfold treeTheta
  have := Real.rpow_nonneg (torusParabolicSize_nonneg (z - z')) (-(5 / 2 : ℝ))
  have := Real.rpow_nonneg (torusParabolicSize_nonneg z) (-(5 / 2 : ℝ))
  linarith

theorem i3Psi2S_le_treeTheta (hzz : 0 < torusParabolicSize (z - z')) (hz : 0 < torusParabolicSize z)
    (hz' : 0 < torusParabolicSize z') {η : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 5 / 2) :
    i3Psi2S η z z' ≤ 3 * treeTheta z z' := by
  unfold i3Psi2S
  rw [sub_zero, sub_zero]
  have := rpow_zz_le_treeTheta hzz hη hη'
  have := rpow_z_le_treeTheta (z' := z') hz hη hη'
  have := rpow_z'_le_treeTheta (z := z) hz' hη hη'
  linarith

theorem rpow_zz_mul_S_le_treeTheta (hzz : 0 < torusParabolicSize (z - z'))
    (hz : 0 < torusParabolicSize z) (hz' : 0 < torusParabolicSize z') {a η : ℝ} (ha : 0 ≤ a)
    (ha' : a ≤ 5 / 4) (hη : 0 ≤ η) (hη' : η ≤ 5 / 4) :
    torusParabolicSize (z - z') ^ (-a) * i3Psi2S η z z' ≤ 6 * treeTheta z z' := by
  unfold i3Psi2S
  rw [sub_zero, sub_zero]
  have t1 := rpow_neg_mul_rpow_neg_le_clean hzz hzz ha hη ha' hη'
  have t2 := rpow_neg_mul_rpow_neg_le_clean hzz hz ha hη ha' hη'
  have t3 := rpow_neg_mul_rpow_neg_le_clean hzz hz' ha hη ha' hη'
  have h1 := treeTheta_ge_one z z'
  unfold treeTheta at h1 ⊢
  have := Real.rpow_nonneg (torusParabolicSize_nonneg (z - z')) (-(5 / 2 : ℝ))
  have := Real.rpow_nonneg (torusParabolicSize_nonneg z) (-(5 / 2 : ℝ))
  have := Real.rpow_nonneg (torusParabolicSize_nonneg z') (-(5 / 2 : ℝ))
  calc _ = torusParabolicSize (z - z') ^ (-a) * torusParabolicSize (z - z') ^ (-η) +
        torusParabolicSize (z - z') ^ (-a) * torusParabolicSize z ^ (-η) +
        torusParabolicSize (z - z') ^ (-a) * torusParabolicSize z' ^ (-η) := by ring
    _ ≤ _ := by nlinarith

theorem rpow_z_mul_z'_le_treeTheta (hz : 0 < torusParabolicSize z) (hz' : 0 < torusParabolicSize z')
    {a b : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 5 / 4) (hb : 0 ≤ b) (hb' : b ≤ 5 / 4) :
    torusParabolicSize z ^ (-a) * torusParabolicSize z' ^ (-b) ≤ 2 * treeTheta z z' := by
  have t := rpow_neg_mul_rpow_neg_le_clean hz hz' ha hb ha' hb'
  unfold treeTheta
  have := Real.rpow_nonneg (torusParabolicSize_nonneg (z - z')) (-(5 / 2 : ℝ))
  have := Real.rpow_nonneg (torusParabolicSize_nonneg z) (-(5 / 2 : ℝ))
  have := Real.rpow_nonneg (torusParabolicSize_nonneg z') (-(5 / 2 : ℝ))
  linarith

end

end RegularityStructures

end
