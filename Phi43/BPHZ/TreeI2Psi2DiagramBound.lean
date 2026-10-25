/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2DiagramZero
public import RegularityStructures.BPHZ.TreeI2Psi2DiagramAlg

/-!
# Chaos `4` of the tree `I(Ψ²) Ψ²`: deterministic bound

[Hai14, (10.39)-(10.42), p. 169].  See `abs_integral_chaos4_le`.
-/

public section

open MeasureTheory

namespace RegularityStructures

theorem abs_le_one_of_torusParabolicSize_le_one {u : SpaceTime} (h : torusParabolicSize u ≤ 1) :
    |u.1| ≤ 1 := by
  by_contra hc
  have h1 : 1 < √|u.1| := by
    rw [Real.lt_sqrt zero_le_one]; norm_num; exact not_le.1 hc
  have h2 := torusSpatialNorm_nonneg u.2
  unfold torusParabolicSize at h
  linarith

theorem torusParabolicSize_sub_le_of_sub {x y y' : SpaceTime} :
    torusParabolicSize (y - y') ≤ 8 * (torusParabolicSize (y - x) + torusParabolicSize (y' - x)) := by
  have h := torusParabolicSize_sub_le_eight_mul (y - x) (y' - x)
  have e : y - x - (y' - x) = y - y' := by abel
  rwa [e] at h

theorem abs_chaos4_pointwise (a a' c02 c03 c12 c13 : ℝ) :
    |a * a' * (4 * c02 ^ 2 * c13 ^ 2 + 4 * c03 ^ 2 * c12 ^ 2 + 16 * (c02 * c03 * c12 * c13))| ≤
      4 * c13 ^ 2 * (|a| * |a'| * c02 ^ 2) + 4 * ((|a| * c03 ^ 2) * (|a'| * c12 ^ 2)) +
        16 * |c13| * (|a| * |a'| * (|c03| * |c02| * |c12|)) := by
  have h1 : |4 * c02 ^ 2 * c13 ^ 2 + 4 * c03 ^ 2 * c12 ^ 2 + 16 * (c02 * c03 * c12 * c13)| ≤
      4 * c02 ^ 2 * c13 ^ 2 + 4 * c03 ^ 2 * c12 ^ 2 + 16 * (|c03| * |c02| * |c12| * |c13|) := by
    refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · rw [abs_of_nonneg (by positivity)]
    · rw [abs_of_nonneg (by positivity)]
    · rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 16)]
      simp only [abs_mul]
      exact le_of_eq (by ring)
  rw [abs_mul, abs_mul]
  have hA : 0 ≤ |a| * |a'| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  calc |a| * |a'| * |4 * c02 ^ 2 * c13 ^ 2 + 4 * c03 ^ 2 * c12 ^ 2 + 16 * (c02 * c03 * c12 * c13)|
      ≤ |a| * |a'| * (4 * c02 ^ 2 * c13 ^ 2 + 4 * c03 ^ 2 * c12 ^ 2 +
        16 * (|c03| * |c02| * |c12| * |c13|)) := mul_le_mul_of_nonneg_left h1 hA
    _ = _ := by ring

end RegularityStructures

end
