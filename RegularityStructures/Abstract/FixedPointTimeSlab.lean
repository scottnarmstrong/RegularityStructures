/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Time slabs in parabolic space-time

The concrete slabs of [Hai14, §7.1] on `ℝ⁴ = ℝ × ℝ³`: `P = {t = 0}`, the distance to `P` for the
parabolic size `‖z‖_𝔰 = |z₀|^{1/2} + ∑ᵢ |zᵢ|` is `timeZeroDist z = |z₀|^{1/2}`
(`timeZeroDist_le_parabolicNorm_sub`, `exists_parabolicNorm_sub_eq_timeZeroDist`), and the slab
`(0, T] × ℝ³` is `timeSlab T`.

These discharge the slab hypotheses of the abstract fixed-point theorems with `𝔰₀ = 2`:

* `timeZeroDist_le_rpow_of_mem_timeSlab`: `ρ ≤ T^{1/2}` on the slab (the short-time gain is
  `T^{κ/2}`);
* `timeSlab_mono`, `timeSlab_zero`: the slabs increase and `S_0 = ∅`;
* `measurableSet_timeSlab_pos`: measurability of `S_T⁺ = S_T ∩ {ρ > 0}`.

Source: [Hai14] = arXiv:1303.5113v4, §7.1 (`P = {(t, x) : t = 0}`, `O_T`).
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The distance `|z₀|^{1/2}` from `z` to the time-zero hyperplane `P = {t = 0}`. -/
def timeZeroDist (z : ParabolicSpace) : ℝ := Real.sqrt |z.1|

/-- The time slab `(0, T] × ℝ³`. -/
def timeSlab (T : ℝ) : Set ParabolicSpace := {z | 0 < z.1 ∧ z.1 ≤ T}

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

theorem timeZeroDist_pos_of_mem_timeSlab {T : ℝ} {z : ParabolicSpace} (hz : z ∈ timeSlab T) :
    0 < timeZeroDist z :=
  Real.sqrt_pos.2 (abs_pos.2 hz.1.ne')

/-- On the slab `(0, T] × ℝ³`: `ρ(z) = |z₀|^{1/2} ≤ T^{1/2}`. -/
theorem timeZeroDist_le_rpow_of_mem_timeSlab {T : ℝ} {z : ParabolicSpace}
    (hz : z ∈ timeSlab T) : timeZeroDist z ≤ T ^ (2 : ℝ)⁻¹ := by
  have hT : 0 ≤ T := hz.1.le.trans hz.2
  rw [timeZeroDist, abs_of_pos hz.1, Real.sqrt_eq_rpow, one_div]
  exact Real.rpow_le_rpow hz.1.le hz.2 (by norm_num)

theorem measurableSet_timeSlab (T : ℝ) : MeasurableSet (timeSlab T) :=
  (measurableSet_lt measurable_const measurable_fst).inter
    (measurableSet_le measurable_fst measurable_const)

end RegularityStructures

end
