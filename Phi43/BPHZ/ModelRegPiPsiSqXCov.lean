/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ModelRegPiPsiSqXPeriodise
public import Phi43.BPHZ.SemigroupTestWickCov
public import Phi43.BPHZ.SemigroupTestDiffWick
public import Phi43.BPHZ.SemigroupTestWick

/-!
# Second moments of the Wick square tested against the coordinate-weighted kernel

With `g_i = semigroupPeriodisedX t x i` (the periodisation of `Q_t(x, y)(yᵢ - xᵢ)`), `t ∈ (0, 1]`
and `lam = t^(1/4)`:

* `E|∫ :Ψ²:_ε g_i|² ≤ C` (`hairerPsiWickSquare_semigroupPeriodisedX_second_moment_le`);
* `E|∫ (:Ψ²:_ε - :Ψ²:_ε') g_i|² ≤ C (max ε ε')^(2θ) lam^(-2θ)`
  (`hairerPsiWickSquare_sub_semigroupPeriodisedX_second_moment_le`).

The function `lam⁻¹ g_i` is a test profile, so the covariance mechanism of
`exists_semigroupPeriodised_second_moment_le_cov` applies (generalised to arbitrary profiles in
`second_moment_le_cov_of_profile`) and gives `lam² · lam^e` with `e = -2`, resp. `-(2 + 2θ)`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **Second moment of a field tested against a profile, from a covariance bound.** -/
theorem second_moment_le_cov_of_profile {e : ℝ} (he : -5 < e) (B : ℝ) (Mom : ℝ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {Y : Ω → SpaceTime → ℝ}, (Measurable fun q : Ω × SpaceTime => Y q.1 q.2) →
      (∀ u, MemLp (fun ω => Y ω u) 2 P) → ∀ {M : ℝ}, (∀ u, ∫ ω, Y ω u * Y ω u ∂P ≤ M) →
      ∀ {Φ : SpaceTime → SpaceTime → ℝ}, (∀ u v, ∫ ω, Y ω u * Y ω v ∂P = Φ u v) →
      ∀ {A : ℝ}, 0 ≤ A → (∀ u v, 0 < torusParabolicSize (u - v) →
        |Φ u v| ≤ A * torusParabolicSize (u - v) ^ e) →
      ∀ {x₀ : SpaceTime} {lam : ℝ} {g : SpaceTime → ℝ}, SemigroupTestProfile x₀ lam B Mom g →
      0 < lam →
        ∫ ω, |∫ w, Y ω w * g w| ^ 2 ∂P ≤ C * A * lam ^ e := by
  refine ⟨max (semigroupTestDoubleConst B Mom 0 e) 0, le_max_right _ _, ?_⟩
  intro Ω _ P _ Y hY hL2 M hM Φ hcov A hA hΦ x₀ lam g hg hlam0
  obtain ⟨hint, hle⟩ := hg.integral_double_le (ζ := 0) (e := e) (by norm_num) he hlam0
  have hlam : 0 < lam ^ e := Real.rpow_pos_of_pos hlam0 _
  have key := secondMoment_le_integral_abs_cov (P := P) hY hL2 hM hcov hg.integrable
  refine key.trans ?_
  have hmaj : Integrable (fun w : SpaceTime × SpaceTime =>
      A * (|g w.1| * |g w.2| *
        (torusParabolicSize (w.1 - x₀) ^ (0 : ℝ) *
          torusParabolicSize (w.1 - w.2) ^ e))) := hint.const_mul A
  have hnn : ∀ w : SpaceTime × SpaceTime, 0 ≤ |g w.1| * |g w.2| * |Φ w.1 w.2| := fun w =>
    mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)
  have hae : ∀ᵐ w : SpaceTime × SpaceTime ∂volume,
      |g w.1| * |g w.2| * |Φ w.1 w.2| ≤
      A * (|g w.1| * |g w.2| *
        (torusParabolicSize (w.1 - x₀) ^ (0 : ℝ) * torusParabolicSize (w.1 - w.2) ^ e)) := by
    filter_upwards [SemigroupTestProfile.ae_pos_pair x₀] with w hw
    have hq := hΦ w.1 w.2 hw.2
    have hgg : 0 ≤ |g w.1| * |g w.2| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
    rw [Real.rpow_zero, one_mul]
    calc _ ≤ |g w.1| * |g w.2| * (A * torusParabolicSize (w.1 - w.2) ^ e) :=
          mul_le_mul_of_nonneg_left hq hgg
      _ = _ := by ring
  calc ∫ q : SpaceTime × SpaceTime, |g q.1| * |g q.2| * |Φ q.1 q.2|
      ≤ ∫ w : SpaceTime × SpaceTime,
        A * (|g w.1| * |g w.2| *
          (torusParabolicSize (w.1 - x₀) ^ (0 : ℝ) * torusParabolicSize (w.1 - w.2) ^ e)) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall hnn) hmaj hae
    _ = A * ∫ w : SpaceTime × SpaceTime,
          |g w.1| * |g w.2| *
            (torusParabolicSize (w.1 - x₀) ^ (0 : ℝ) * torusParabolicSize (w.1 - w.2) ^ e) :=
        integral_const_mul _ _
    _ ≤ A * (semigroupTestDoubleConst B Mom 0 e * lam ^ (0 + e : ℝ)) :=
        mul_le_mul_of_nonneg_left hle hA
    _ ≤ A * (max (semigroupTestDoubleConst B Mom 0 e) 0 * lam ^ (0 + e : ℝ)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_) hA
        rw [zero_add]; exact hlam.le
    _ = max (semigroupTestDoubleConst B Mom 0 e) 0 * A * lam ^ e := by rw [zero_add]; ring

theorem sq_mul_rpow_eq_rpow_add {l e : ℝ} (hl : 0 < l) : l ^ 2 * l ^ e = l ^ (2 + e) := by
  rw [← Real.rpow_natCast, ← Real.rpow_add hl]
  norm_num

/-- Rescaling of a tested second moment: `∫ |∫ Y g|² = c² ∫ |∫ Y (c⁻¹ g)|²`. -/
theorem integral_sq_tested_scale {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (Y : Ω → SpaceTime → ℝ) (g : SpaceTime → ℝ) {c : ℝ} (hc : c ≠ 0) :
    ∫ ω, |∫ w, Y ω w * g w| ^ 2 ∂P =
      c ^ 2 * ∫ ω, |∫ w, Y ω w * (c⁻¹ * g w)| ^ 2 ∂P := by
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  have : ∫ w, Y ω w * (c⁻¹ * g w) = c⁻¹ * ∫ w, Y ω w * g w := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun w => by dsimp only; ring)
  dsimp only
  rw [this]
  simp only [abs_mul, mul_pow, sq_abs]
  field_simp

end RegularityStructures.Phi43

end
