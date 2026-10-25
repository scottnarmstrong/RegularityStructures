/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestCov
public import Phi43.BPHZ.SemigroupTestSup
public import Phi43.BPHZ.SemigroupTestMoment

/-!
# The periodised semigroup kernel is a test profile

For `t ∈ (0, 1]`, `lam = t^(1/4)` and a point `x ∈ ℝ⁴`, the periodised kernel
`u ↦ q^♯_t(x, u)` on `ℝ × T³` is a `SemigroupTestProfile` at base point `proj x` and scale `lam`,
with constants `B` (sup bound, `exists_abs_semigroupPeriodised_le`) and
`Mom r = parabolicMomentConst r` (moments, `integral_abs_semigroupPeriodised_mul_le`), uniformly
in `t, x`.  Consequently the chaos-reduction integrals of `SemigroupTestDouble` and
`SemigroupTestCov` hold for `q^♯_t(x, ·)` with constants independent of `t ≤ 1` and `x`.
-/

public section

open MeasureTheory

namespace RegularityStructures

theorem rpow_quarter_rpow {t : ℝ} (ht : 0 < t) (r : ℝ) :
    (t ^ (1 / 4 : ℝ)) ^ r = t ^ (r / 4) := by
  rw [← Real.rpow_mul ht.le]
  congr 1
  ring

/-- **The periodised semigroup kernel is a test profile.** -/
theorem exists_semigroupTestProfile_semigroupPeriodised :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
      SemigroupTestProfile (Phi43.spaceTimeProj x) (t ^ (1 / 4 : ℝ)) B parabolicMomentConst
        (semigroupPeriodised t x) := by
  obtain ⟨B, hB0, hB⟩ := exists_abs_semigroupPeriodised_le
  refine ⟨B, hB0, fun {t} ht ht1 x => ?_⟩
  refine ⟨measurable_semigroupPeriodised t x, fun u => hB ht ht1 x u, fun r hr => ?_,
    fun r hr => ?_⟩
  · exact (integral_abs_semigroupPeriodised_mul_le ht hr x).1
  · rw [rpow_quarter_rpow ht]
    exact (integral_abs_semigroupPeriodised_mul_le ht hr x).2

/-- **Chaos-reduction integral for `q^♯_t(x, ·)` (concrete form).**  For `ζ, e > -5` there is `C`,
independent of `t ∈ (0, 1]` and `x`, with
`∫∫ |q^♯_t(x, u)| |q^♯_t(x, v)| s(u - proj x)^ζ s(u - v)^e ≤ C (t^(1/4))^(ζ+e)`. -/
theorem exists_integral_double_semigroupPeriodised_le {ζ e : ℝ} (hζ : -5 < ζ) (he : -5 < e) :
    ∃ C : ℝ, ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
      Integrable (fun w : SpaceTime × SpaceTime =>
        |semigroupPeriodised t x w.1| * |semigroupPeriodised t x w.2| *
          (torusParabolicSize (w.1 - Phi43.spaceTimeProj x) ^ ζ *
            torusParabolicSize (w.1 - w.2) ^ e)) ∧
      ∫ w : SpaceTime × SpaceTime,
        |semigroupPeriodised t x w.1| * |semigroupPeriodised t x w.2| *
          (torusParabolicSize (w.1 - Phi43.spaceTimeProj x) ^ ζ *
            torusParabolicSize (w.1 - w.2) ^ e) ≤ C * (t ^ (1 / 4 : ℝ)) ^ (ζ + e) := by
  obtain ⟨B, hB0, hB⟩ := exists_semigroupTestProfile_semigroupPeriodised
  exact ⟨semigroupTestDoubleConst B parabolicMomentConst ζ e, fun {t} ht ht1 x =>
    (hB ht ht1 x).integral_double_le hζ he (Real.rpow_pos_of_pos ht _)⟩

end RegularityStructures

end
