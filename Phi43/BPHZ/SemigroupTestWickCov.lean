/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestAllMomentsSetup
public import Phi43.BPHZ.SemigroupTestPsi

/-!
# Second moments against the periodised semigroup kernel from a covariance bound

If a centred random field `Y` on `ℝ × T³` has covariance `Φ(u, v)` bounded by `A s(u - v)^e`,
`s = torusParabolicSize`, for some `e > -5`, then for `t ∈ (0, 1]`, `lam = t^(1/4)` and every
`x`, `E|∫ Y q^♯_t(x, ·)|² ≤ A C lam^e` with `C = C(e)` independent of `A`, `t`, `x` and `Y`
(`exists_semigroupPeriodised_second_moment_le_cov`).  This is the mechanism behind
`hairerPsiField_semigroupPeriodised_second_moment_le`, with the covariance bound as hypothesis.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **Second moment of a field tested against `q^♯_t(x, ·)` from a covariance bound.** -/
theorem exists_semigroupPeriodised_second_moment_le_cov {e : ℝ} (he : -5 < e) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {Y : Ω → SpaceTime → ℝ}, (Measurable fun q : Ω × SpaceTime => Y q.1 q.2) →
      (∀ u, MemLp (fun ω => Y ω u) 2 P) → ∀ {M : ℝ}, (∀ u, ∫ ω, Y ω u * Y ω u ∂P ≤ M) →
      ∀ {Φ : SpaceTime → SpaceTime → ℝ}, (∀ u v, ∫ ω, Y ω u * Y ω v ∂P = Φ u v) →
      ∀ {A : ℝ}, 0 ≤ A → (∀ u v, 0 < torusParabolicSize (u - v) →
        |Φ u v| ≤ A * torusParabolicSize (u - v) ^ e) →
      ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
        ∫ ω, |∫ w, Y ω w * semigroupPeriodised t x w| ^ 2 ∂P ≤
          C * A * (t ^ (1 / 4 : ℝ)) ^ e := by
  obtain ⟨Cd, hCd⟩ := exists_integral_double_semigroupPeriodised_le (ζ := 0) (e := e)
    (by norm_num) he
  refine ⟨max Cd 0, le_max_right _ _, ?_⟩
  intro Ω _ P _ Y hY hL2 M hM Φ hcov A hA hΦ t ht ht1 x
  obtain ⟨hint, hle⟩ := hCd ht ht1 x
  have hg : Integrable (semigroupPeriodised t x) := (semigroupPeriodised_chaos_data ht x).2
  have hlam : 0 < (t ^ (1 / 4 : ℝ)) ^ e := Real.rpow_pos_of_pos (Real.rpow_pos_of_pos ht _) _
  have key := secondMoment_le_integral_abs_cov (P := P) hY hL2 hM hcov hg
  refine key.trans ?_
  have hmaj : Integrable (fun w : SpaceTime × SpaceTime =>
      A * (|semigroupPeriodised t x w.1| * |semigroupPeriodised t x w.2| *
        (torusParabolicSize (w.1 - spaceTimeProj x) ^ (0 : ℝ) *
          torusParabolicSize (w.1 - w.2) ^ e))) := hint.const_mul A
  have hnn : ∀ w : SpaceTime × SpaceTime, 0 ≤ |semigroupPeriodised t x w.1| *
      |semigroupPeriodised t x w.2| * |Φ w.1 w.2| := fun w =>
    mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)
  have hae : ∀ᵐ w : SpaceTime × SpaceTime ∂volume,
      |semigroupPeriodised t x w.1| * |semigroupPeriodised t x w.2| * |Φ w.1 w.2| ≤
      A * (|semigroupPeriodised t x w.1| * |semigroupPeriodised t x w.2| *
        (torusParabolicSize (w.1 - spaceTimeProj x) ^ (0 : ℝ) *
          torusParabolicSize (w.1 - w.2) ^ e)) := by
    filter_upwards [SemigroupTestProfile.ae_pos_pair (spaceTimeProj x)] with w hw
    have hq := hΦ w.1 w.2 hw.2
    have hgg : 0 ≤ |semigroupPeriodised t x w.1| * |semigroupPeriodised t x w.2| :=
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
    rw [Real.rpow_zero, one_mul]
    calc _ ≤ |semigroupPeriodised t x w.1| * |semigroupPeriodised t x w.2| *
          (A * torusParabolicSize (w.1 - w.2) ^ e) := mul_le_mul_of_nonneg_left hq hgg
      _ = _ := by ring
  calc ∫ q : SpaceTime × SpaceTime, |semigroupPeriodised t x q.1| * |semigroupPeriodised t x q.2| *
        |Φ q.1 q.2|
      ≤ ∫ w : SpaceTime × SpaceTime,
        A * (|semigroupPeriodised t x w.1| * |semigroupPeriodised t x w.2| *
          (torusParabolicSize (w.1 - spaceTimeProj x) ^ (0 : ℝ) *
            torusParabolicSize (w.1 - w.2) ^ e)) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall hnn) hmaj hae
    _ = A * ∫ w : SpaceTime × SpaceTime,
          |semigroupPeriodised t x w.1| * |semigroupPeriodised t x w.2| *
            (torusParabolicSize (w.1 - spaceTimeProj x) ^ (0 : ℝ) *
              torusParabolicSize (w.1 - w.2) ^ e) := integral_const_mul _ _
    _ ≤ A * (Cd * (t ^ (1 / 4 : ℝ)) ^ (0 + e : ℝ)) := mul_le_mul_of_nonneg_left hle hA
    _ ≤ A * (max Cd 0 * (t ^ (1 / 4 : ℝ)) ^ (0 + e : ℝ)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_) hA
        rw [zero_add]; exact hlam.le
    _ = max Cd 0 * A * (t ^ (1 / 4 : ℝ)) ^ e := by rw [zero_add]; ring

end RegularityStructures.Phi43

end
