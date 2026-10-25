/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3PsiChainBasic

/-!
# Symmetrisation of the exponents `s(a - b)^(-δ)`

For the three points `z`, `z'`, `0`, every ordered pair `(a, b)` gives
`s(a - b)^(-δ) ≤ 2 (s(z - z')^(-δ) + s(z - 0)^(-δ) + s(z' - 0)^(-δ))`, using
`s(-x) ≤ 2 s(x)` and that `s(a - a) = 0`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

theorem torusParabolicSize_zero_spaceTime : torusParabolicSize (0 : SpaceTime) = 0 := by
  unfold torusParabolicSize
  simp [torusSpatialNorm_zero]

/-- Positivity of `s(a - b)` is symmetric. -/
theorem torusParabolicSize_sub_pos_symm {a b : SpaceTime} (h : 0 < torusParabolicSize (a - b)) :
    0 < torusParabolicSize (b - a) := by
  have := torusParabolicSize_neg_le_two_mul (b - a)
  rw [neg_sub] at this
  linarith

/-- Flipping the argument of `s^(-δ)` costs a factor at most `2`. -/
theorem torusParabolicSize_rpow_neg_flip_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    {a b : SpaceTime} (h : 0 < torusParabolicSize (a - b)) :
    torusParabolicSize (b - a) ^ (-δ) ≤ 2 * torusParabolicSize (a - b) ^ (-δ) := by
  have hneg := torusParabolicSize_neg_le_two_mul (b - a)
  rw [neg_sub] at hneg
  have hy : 0 < torusParabolicSize (a - b) / 2 := by linarith
  have h1 : torusParabolicSize (b - a) ^ (-δ) ≤ (torusParabolicSize (a - b) / 2) ^ (-δ) :=
    Real.rpow_le_rpow_of_nonpos hy (by linarith) (neg_nonpos.2 hδ0)
  have h2 : (torusParabolicSize (a - b) / 2) ^ (-δ) =
      2 ^ δ * torusParabolicSize (a - b) ^ (-δ) := by
    rw [Real.div_rpow h.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_neg h.le]
    field_simp
  have h3 : (2 : ℝ) ^ δ ≤ 2 := by
    calc (2 : ℝ) ^ δ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hδ1
      _ = 2 := Real.rpow_one 2
  have h4 : 0 ≤ torusParabolicSize (a - b) ^ (-δ) := Real.rpow_nonneg h.le _
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ 2 * torusParabolicSize (a - b) ^ (-δ) := mul_le_mul_of_nonneg_right h3 h4

/-- Every ordered pair among `z, z', 0` is controlled by the symmetric sum. -/
theorem torusParabolicSize_rpow_neg_le_two_mul_sum {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {z z' a b : SpaceTime} (pzz : 0 < torusParabolicSize (z - z'))
    (pz0 : 0 < torusParabolicSize (z - 0)) (pz'0 : 0 < torusParabolicSize (z' - 0))
    (ha : a = z ∨ a = z' ∨ a = 0) (hb : b = z ∨ b = z' ∨ b = 0) :
    torusParabolicSize (a - b) ^ (-δ) ≤ 2 * (torusParabolicSize (z - z') ^ (-δ) +
      torusParabolicSize (z - 0) ^ (-δ) + torusParabolicSize (z' - 0) ^ (-δ)) := by
  have n1 : 0 ≤ torusParabolicSize (z - z') ^ (-δ) := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have n2 : 0 ≤ torusParabolicSize (z - 0) ^ (-δ) := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have n3 : 0 ≤ torusParabolicSize (z' - 0) ^ (-δ) := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have f1 := torusParabolicSize_rpow_neg_flip_le hδ.le hδ1 pzz
  have f2 := torusParabolicSize_rpow_neg_flip_le hδ.le hδ1 pz0
  have f3 := torusParabolicSize_rpow_neg_flip_le hδ.le hδ1 pz'0
  have e0 : ∀ x : SpaceTime, torusParabolicSize (x - x) ^ (-δ) = 0 := by
    intro x
    rw [sub_self, torusParabolicSize_zero_spaceTime]
    exact Real.zero_rpow (neg_ne_zero.2 hδ.ne')
  have g1 := e0 z
  have g2 := e0 z'
  have g3 := e0 (0 : SpaceTime)
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;> rw [ha, hb] <;> linarith

end RegularityStructures

end
