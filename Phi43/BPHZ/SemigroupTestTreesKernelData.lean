/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesSlabAt
public import Phi43.BPHZ.TreeI2Psi2DiagramBound
public import Phi43.BPHZ.TreeI3Psi2DiagramPointwise

/-!
# Kernel data and the recentred kernel on a time slab

`SingularKernelData K Q B` collects the hypotheses on the kernel `K` (measurable, `|K| ≤ B s^(-3)`,
supported in `|t| ≤ 1`) and the covariance `Q` (measurable, `|Q| ≤ B s^(-1)`) used for the crude
global diagram bounds.  `abs_i2Psi2Increment_le_slab` bounds the recentred kernel
`K(y - ·) - K(x - ·)` by `B (s₃(y; ·) + s₃(x; ·))` on the slab
`{|w.1 - x.1| ≤ |y.1 - x.1| + 1}` and shows it vanishes outside.
-/

@[expose] public section

namespace RegularityStructures

/-- Hypotheses on the singular kernel `K` and the covariance `Q` for the global diagram bounds. -/
structure SingularKernelData (K Q : SpaceTime → ℝ) (B : ℝ) : Prop where
  nonneg : 0 ≤ B
  measurable_K : Measurable K
  measurable_Q : Measurable Q
  K_bound : ∀ z, 0 < torusParabolicSize z → |K z| ≤ B * torusParabolicSize z ^ (-(3 : ℝ))
  K_supp : ∀ z : SpaceTime, 1 < |z.1| → K z = 0
  Q_bound : ∀ z, 0 < torusParabolicSize z → |Q z| ≤ B * torusParabolicSize z ^ (-(1 : ℝ))

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

theorem i2Psi2Increment_eq_zero_of_abs_lt {K : SpaceTime → ℝ}
    (hKs : ∀ z : SpaceTime, 1 < |z.1| → K z = 0) {x y w : SpaceTime}
    (hw : |y.1 - x.1| + 1 < |w.1 - x.1|) : i2Psi2Increment K x y w = 0 := by
  have e1 : K (y - w) = 0 := by
    apply hKs
    have : (y - w).1 = y.1 - w.1 := rfl
    rw [this]
    have h := abs_sub_abs_le_abs_sub (w.1 - x.1) (y.1 - x.1)
    have h2 : |(w.1 - x.1) - (y.1 - x.1)| = |y.1 - w.1| := by
      rw [show (w.1 - x.1) - (y.1 - x.1) = -(y.1 - w.1) by ring, abs_neg]
    rw [h2] at h
    linarith
  have e2 : K (x - w) = 0 := by
    apply hKs
    have : (x - w).1 = x.1 - w.1 := rfl
    rw [this, abs_sub_comm]
    linarith [abs_nonneg (y.1 - x.1)]
  unfold i2Psi2Increment
  rw [e1, e2, sub_zero]

/-- The recentred kernel is dominated by `B (s₃(y; w) + s₃(x; w))` on the slab and vanishes
outside. -/
theorem abs_i2Psi2Increment_le_slab {K Q : SpaceTime → ℝ} {B : ℝ} (h : SingularKernelData K Q B)
    {x y w : SpaceTime} (h1 : 0 < torusParabolicSize (y - w))
    (h2 : 0 < torusParabolicSize (x - w)) :
    |i2Psi2Increment K x y w| ≤ Set.indicator {w : SpaceTime | |w.1 - x.1| ≤ |y.1 - x.1| + 1}
      (fun w => B * (singularPow 3 y w + singularPow 3 x w)) w := by
  by_cases hw : w ∈ {w : SpaceTime | |w.1 - x.1| ≤ |y.1 - x.1| + 1}
  · rw [Set.indicator_of_mem hw]
    unfold i2Psi2Increment
    calc |K (y - w) - K (x - w)| ≤ |K (y - w)| + |K (x - w)| := abs_sub _ _
      _ ≤ B * torusParabolicSize (y - w) ^ (-(3 : ℝ)) + B * torusParabolicSize (x - w) ^ (-(3 : ℝ)) :=
          add_le_add (h.K_bound _ h1) (h.K_bound _ h2)
      _ = _ := by simp only [singularPow]; ring
  · rw [Set.indicator_of_notMem hw]
    have : |y.1 - x.1| + 1 < |w.1 - x.1| := not_le.1 hw
    rw [i2Psi2Increment_eq_zero_of_abs_lt h.K_supp this, abs_zero]

theorem SingularKernelData.measurable_increment {K Q : SpaceTime → ℝ} {B : ℝ}
    (h : SingularKernelData K Q B) (x y : SpaceTime) :
    Measurable (i2Psi2Increment K x y) :=
  measurable_i2Psi2Increment h.measurable_K x y

end RegularityStructures

end
