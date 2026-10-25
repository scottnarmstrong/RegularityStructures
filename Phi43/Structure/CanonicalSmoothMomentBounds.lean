/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalSmoothGrowth

/-!
# Whole-space Q bounds from cancellation and polynomial tails

An auxiliary estimate for Hairer [Hai14, Proposition 8.27] in Hoshino's
weighted framework [Hos25, Definition 2.1]. A second, higher power controls
the far field without weakening the small-scale exponent.
-/

public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

/-- Two pointwise powers yield the lower of their Q scaling exponents.
This helper separates the local cancellation and polynomial-tail estimates. -/
theorem canonicalSmooth_apply_two_power_bound {g : ParabolicSpace → ℝ}
    (hg : PolyBounded g) (x : ParabolicSpace) {a b A B : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ y, |g y| ≤ A * parabolicNorm (y - x) ^ a +
      B * parabolicNorm (y - x) ^ b)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    |parabolicSemigroup.apply t g x| ≤
      (A * parabolicSemigroup.momentConst a + B * parabolicSemigroup.momentConst b) *
        t ^ (a / parabolicSemigroup.order) := by
  have hb := ha.trans hab
  have hiA := (parabolicSemigroup.integrable_moment ht ha x).const_mul A
  have hiB := (parabolicSemigroup.integrable_moment ht hb x).const_mul B
  have htp : t ^ (b / parabolicSemigroup.order) ≤ t ^ (a / parabolicSemigroup.order) :=
    Real.rpow_le_rpow_of_exponent_ge ht ht1
      (div_le_div_of_nonneg_right hab parabolicSemigroup.order_pos.le)
  calc
    |parabolicSemigroup.apply t g x| ≤ ∫ y, |parabolicKernel t (x - y) * g y| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ y, A * (|parabolicSemigroup.kernel t x y| *
          parabolicSemigroup.scaleDist y x ^ a) +
        B * (|parabolicSemigroup.kernel t x y| *
          parabolicSemigroup.scaleDist y x ^ b) := by
      apply integral_mono (hg.integrable_parabolicKernel_mul ht x).abs (hiA.add hiB)
      intro y
      dsimp only [Pi.add_apply]
      rw [abs_mul]
      calc
        _ ≤ |parabolicKernel t (x - y)| * (A * parabolicNorm (y - x) ^ a +
            B * parabolicNorm (y - x) ^ b) :=
          mul_le_mul_of_nonneg_left (hbound y) (abs_nonneg _)
        _ = _ := by
          change _ = A * (|parabolicKernel t (x - y)| * parabolicNorm (y - x) ^ a) +
            B * (|parabolicKernel t (x - y)| * parabolicNorm (y - x) ^ b)
          ring
    _ = A * (∫ y, |parabolicSemigroup.kernel t x y| *
          parabolicSemigroup.scaleDist y x ^ a) +
        B * (∫ y, |parabolicSemigroup.kernel t x y| *
          parabolicSemigroup.scaleDist y x ^ b) := by
      rw [integral_add hiA hiB, integral_const_mul, integral_const_mul]
    _ ≤ A * (parabolicSemigroup.momentConst a * t ^ (a / parabolicSemigroup.order)) +
        B * (parabolicSemigroup.momentConst b * t ^ (b / parabolicSemigroup.order)) :=
      add_le_add (mul_le_mul_of_nonneg_left (parabolicSemigroup.moment_le ht ha x) hA)
        (mul_le_mul_of_nonneg_left (parabolicSemigroup.moment_le ht hb x) hB)
    _ ≤ A * (parabolicSemigroup.momentConst a * t ^ (a / parabolicSemigroup.order)) +
        B * (parabolicSemigroup.momentConst b * t ^ (a / parabolicSemigroup.order)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left htp (parabolicSemigroup.momentConst_nonneg b)) hB)
    _ = _ := by ring

end RegularityStructures.Phi43

end
