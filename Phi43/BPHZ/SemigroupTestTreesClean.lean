/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesSlab
public import Phi43.BPHZ.TreeI2Psi2DiagramCov

/-!
# Clean-up inequalities for negative powers of the parabolic size

For `s > 0`, `s^(-e) ≤ s^(-(5/2)) + 1` if `0 ≤ e ≤ 5/2`, and for `0 ≤ a, b ≤ 5/4`,
`s^(-a) t^(-b) ≤ s^(-(5/2)) + t^(-(5/2)) + 2`.  These allow every singular product of a global
diagram bound to be dominated by `treeTheta z z' = s(z - z')^(-5/2) + s(z)^(-5/2) + s(z')^(-5/2) + 1`.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The common singular majorant `s(z - z')^(-5/2) + s(z)^(-5/2) + s(z')^(-5/2) + 1`. -/
def treeTheta (z z' : SpaceTime) : ℝ :=
  torusParabolicSize (z - z') ^ (-(5 / 2 : ℝ)) + torusParabolicSize z ^ (-(5 / 2 : ℝ)) +
    torusParabolicSize z' ^ (-(5 / 2 : ℝ)) + 1

end RegularityStructures

end

public section

namespace RegularityStructures

theorem rpow_neg_le_five_halves_add_one {s e : ℝ} (hs : 0 < s) (he : 0 ≤ e)
    (he' : e ≤ 5 / 2) : s ^ (-e) ≤ s ^ (-(5 / 2 : ℝ)) + 1 := by
  rcases le_total s 1 with h | h
  · have : s ^ (-e) ≤ s ^ (-(5 / 2 : ℝ)) := Real.rpow_le_rpow_of_exponent_ge hs h (by linarith)
    have := Real.rpow_nonneg hs.le (-(5 / 2 : ℝ))
    linarith
  · have : s ^ (-e) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h (by linarith)
    have := Real.rpow_nonneg hs.le (-(5 / 2 : ℝ))
    linarith

theorem rpow_neg_mul_rpow_neg_le_clean {s t a b : ℝ} (hs : 0 < s) (ht : 0 < t) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (ha' : a ≤ 5 / 4) (hb' : b ≤ 5 / 4) :
    s ^ (-a) * t ^ (-b) ≤ s ^ (-(5 / 2 : ℝ)) + t ^ (-(5 / 2 : ℝ)) + 2 := by
  have e1 : (s ^ (-a)) ^ 2 = s ^ (-(2 * a)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]; norm_num; ring_nf
  have e2 : (t ^ (-b)) ^ 2 = t ^ (-(2 * b)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]; norm_num; ring_nf
  have h1 := rpow_neg_le_five_halves_add_one hs (by linarith : 0 ≤ 2 * a) (by linarith)
  have h2 := rpow_neg_le_five_halves_add_one ht (by linarith : 0 ≤ 2 * b) (by linarith)
  have := two_mul_le_add_sq (s ^ (-a)) (t ^ (-b))
  rw [e1] at *
  nlinarith [Real.rpow_nonneg hs.le (-(5 / 2 : ℝ)), Real.rpow_nonneg ht.le (-(5 / 2 : ℝ))]

theorem treeTheta_nonneg (z z' : SpaceTime) : 0 ≤ treeTheta z z' := by
  unfold treeTheta
  have := Real.rpow_nonneg (torusParabolicSize_nonneg (z - z')) (-(5 / 2 : ℝ))
  have := Real.rpow_nonneg (torusParabolicSize_nonneg z) (-(5 / 2 : ℝ))
  have := Real.rpow_nonneg (torusParabolicSize_nonneg z') (-(5 / 2 : ℝ))
  linarith

theorem treeTheta_ge_one (z z' : SpaceTime) : 1 ≤ treeTheta z z' := by
  unfold treeTheta
  have := Real.rpow_nonneg (torusParabolicSize_nonneg (z - z')) (-(5 / 2 : ℝ))
  have := Real.rpow_nonneg (torusParabolicSize_nonneg z) (-(5 / 2 : ℝ))
  have := Real.rpow_nonneg (torusParabolicSize_nonneg z') (-(5 / 2 : ℝ))
  linarith

end RegularityStructures

end
