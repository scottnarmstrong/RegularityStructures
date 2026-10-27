/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.TimeFreeGeometry

/-! The vertical bridge recovering future pairs in the radius-local Schauder estimate. The construction
uses only the source parabolic metric and leaves the terminal face untouched. -/
@[expose] public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures Set MW20

/-- The bridge has y's spatial coordinate and lies rho² before x. -/
def verticalBridge (x y : ParabolicSpace) : ParabolicSpace :=
  (x.1 - pdist x y ^ 2, y.2)

theorem verticalBridge_distance_left (x y : ParabolicSpace) :
    pdist x (verticalBridge x y) = pdist x y := by
  have ht : x.1 - (x.1 - pdist x y ^ 2) = pdist x y ^ 2 := by ring
  change max (Real.sqrt |x.1 - (x.1 - pdist x y ^ 2)|) ‖x.2 - y.2‖ = pdist x y
  rw [ht, abs_of_nonneg (sq_nonneg _), Real.sqrt_sq (pdist_nonneg x y)]
  exact max_eq_left (le_max_right _ _)

theorem verticalBridge_time_lt {x y : ParabolicSpace}
    (hρ : 0 < pdist x y) (hfuture : x.1 ≤ y.1) :
    (verticalBridge x y).1 < x.1 ∧ (verticalBridge x y).1 < y.1 := by
  change x.1 - pdist x y ^ 2 < x.1 ∧ x.1 - pdist x y ^ 2 < y.1
  constructor <;> nlinarith [sq_pos_of_pos hρ]

theorem verticalBridge_distance_right {x y : ParabolicSpace} (hfuture : x.1 ≤ y.1) :
    pdist y (verticalBridge x y) ≤ Real.sqrt 2 * pdist x y := by
  have hρ := pdist_nonneg x y
  have ht : |x.1 - y.1| ≤ pdist x y ^ 2 :=
    (Real.sqrt_le_left hρ).mp (le_max_left _ _)
  have hdiff : y.1 - x.1 ≤ pdist x y ^ 2 := by
    have h := le_abs_self (y.1 - x.1)
    rw [abs_sub_comm] at h
    exact h.trans ht
  change max (Real.sqrt |y.1 - (x.1 - pdist x y ^ 2)|) ‖y.2 - y.2‖ ≤ _
  rw [sub_self, norm_zero, max_eq_left (Real.sqrt_nonneg _)]
  calc
    _ ≤ Real.sqrt (2 * pdist x y ^ 2) := by
      apply Real.sqrt_le_sqrt
      rw [abs_of_nonneg (by nlinarith [sq_nonneg (pdist x y)])]
      linarith
    _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq hρ]

theorem verticalBridge_distance_right_lt {x y : ParabolicSpace} {d : ℝ}
    (hd : 0 < d) (hfuture : x.1 ≤ y.1) (hsmall : pdist x y ≤ d / 8) :
    pdist y (verticalBridge x y) < d / 4 := by
  have hs : Real.sqrt 2 < 2 := (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
  calc
    _ ≤ Real.sqrt 2 * pdist x y := verticalBridge_distance_right hfuture
    _ ≤ Real.sqrt 2 * (d / 8) := mul_le_mul_of_nonneg_left hsmall (Real.sqrt_nonneg _)
    _ < 2 * (d / 8) := mul_lt_mul_of_pos_right hs (by linarith)
    _ = _ := by ring

/-- The bridge lies in D_(d/2) even when y is on the future side of x.
No top-face distance or global field assumption is used. -/
theorem verticalBridge_interior_half {r d : ℝ} {x y : ParabolicSpace}
    (hd : 0 < d) (hx : x ∈ cylinderInterior r d) (hy : y ∈ cylinderInterior r d)
    (hsmall : pdist x y ≤ d / 8) :
    verticalBridge x y ∈ cylinderInterior r (d / 2) := by
  have hsq : pdist x y ^ 2 ≤ (d / 8) ^ 2 :=
    pow_le_pow_left₀ (pdist_nonneg x y) hsmall 2
  change r ^ 2 + (d / 2) ^ 2 < x.1 - pdist x y ^ 2 ∧
    x.1 - pdist x y ^ 2 < 1 ∧
    ∀ i : Fin 3, -1 + r + d / 2 < y.2 i ∧ y.2 i < 1 - r - d / 2
  refine ⟨by nlinarith [hx.1], by nlinarith [hx.2.1, sq_nonneg (pdist x y)], ?_⟩
  intro i
  obtain ⟨hl, hu⟩ := hy.2.2 i
  constructor <;> linarith

end GlobalPhi43.Local
