/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreePsiMoment
public import Phi43.BPHZ.SemigroupTestKernel
public import RegularityStructures.BPHZ.SemigroupTestSecondMoment

/-!
# Second moment of the tree `Ψ` tested against the periodised semigroup kernel

For the regularised tree `Ψ_ε = hairerPsiField`, a point `x ∈ ℝ⁴`, `t ∈ (0, 1]` and
`lam = t^(1/4)`,
`E|∫_{ℝ × T³} Ψ_ε(w) q^♯_t(x, w) dw|² ≤ C lam⁻¹`
with `C` independent of `ε ∈ (0, 1]`, `t ∈ (0, 1]` and `x`
(`hairerPsiField_semigroupPeriodised_second_moment_le`).  There is no restriction `lam ≤ 1/3` and
no compact support of the test function: the covariance bound `|Q_ε(z)| ≲ s(z)⁻¹` holds globally,
and the tails of `q^♯_t(x, ·)` are controlled by `SemigroupTestProfile.integral_double_le`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **Second moment of the tested tree `Ψ`, semigroup test.**  Uniform in
`ε ∈ (0, 1]`, `t ∈ (0, 1]` and `x ∈ ℝ⁴`. -/
theorem hairerPsiField_semigroupPeriodised_second_moment_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
        ∫ ω, |∫ w, hairerPsiField N ξ ω w * semigroupPeriodised t x w| ^ 2 ∂P ≤
          C * (t ^ (1 / 4 : ℝ)) ^ (-(1 : ℝ)) := by
  obtain ⟨A, hA, hQ⟩ := hairerCovariance_abs_le N ρ hρ
  obtain ⟨B, hB0, hB⟩ := exists_semigroupTestProfile_semigroupPeriodised
  set Cd : ℝ := semigroupTestDoubleConst B parabolicMomentConst 0 (-1) with hCd
  have hCd0 : 0 ≤ Cd := by
    have h1 := parabolicMomentConst_nonneg 0
    have h2 : (0 : ℝ) < 5 + -1 := by norm_num
    simp only [hCd, semigroupTestDoubleConst, semigroupTestMomConst, show (-1 : ℝ) < 0 by norm_num,
      ↓reduceIte, le_refl]
    positivity
  refine ⟨A * Cd, mul_nonneg hA hCd0, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ t ht ht1 x
  have := hW.isProbabilityMeasure
  have h := hB ht ht1 x
  have hlam : 0 < t ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos ht _
  have hR : Measurable (hairerCovariance N ρ ε) :=
    constantsComparison_hairerCovariance_measurable N ρ hε.1 hρ hε.2
  have hcov := hairerPsiField_integral_mul N hρ hε.1 hW hξ
  have key := secondMoment_le_integral_abs_cov (P := P) (Y := hairerPsiField N ξ)
    (measurable_hairerPsiField_uncurry N hξ) (fun u => hairerPsiField_memLp N hρ hε.1 hW hξ u)
    (M := hairerCovariance N ρ ε 0) (fun u => by rw [hcov u u, sub_self])
    (Φ := fun u v => hairerCovariance N ρ ε (u - v)) hcov h.integrable
  refine key.trans ?_
  have hdbl := h.integral_double_le (ζ := 0) (e := -1) (by norm_num) (by norm_num) hlam
  have hmaj : Integrable (fun w : SpaceTime × SpaceTime =>
      A * (|semigroupPeriodised t x w.1| * |semigroupPeriodised t x w.2| *
        (torusParabolicSize (w.1 - spaceTimeProj x) ^ (0 : ℝ) *
          torusParabolicSize (w.1 - w.2) ^ (-1 : ℝ)))) := hdbl.1.const_mul A
  have hnn : ∀ w : SpaceTime × SpaceTime, 0 ≤ |semigroupPeriodised t x w.1| *
      |semigroupPeriodised t x w.2| * |hairerCovariance N ρ ε (w.1 - w.2)| := fun w =>
    mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)
  have hae : ∀ᵐ w : SpaceTime × SpaceTime ∂volume,
      |semigroupPeriodised t x w.1| * |semigroupPeriodised t x w.2| *
        |hairerCovariance N ρ ε (w.1 - w.2)| ≤
      A * (|semigroupPeriodised t x w.1| * |semigroupPeriodised t x w.2| *
        (torusParabolicSize (w.1 - spaceTimeProj x) ^ (0 : ℝ) *
          torusParabolicSize (w.1 - w.2) ^ (-1 : ℝ))) := by
    filter_upwards [SemigroupTestProfile.ae_pos_pair (spaceTimeProj x)] with w hw
    have hq := hQ hε.1 hε.2 (w.1 - w.2) hw.2
    have hgg : 0 ≤ |semigroupPeriodised t x w.1| * |semigroupPeriodised t x w.2| :=
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
    rw [Real.rpow_zero, one_mul, Real.rpow_neg_one]
    rw [Real.rpow_neg_one] at hq
    calc _ ≤ |semigroupPeriodised t x w.1| * |semigroupPeriodised t x w.2| *
          (A * (torusParabolicSize (w.1 - w.2))⁻¹) := mul_le_mul_of_nonneg_left hq hgg
      _ = _ := by ring
  calc ∫ q : SpaceTime × SpaceTime, |semigroupPeriodised t x q.1| * |semigroupPeriodised t x q.2| *
        |hairerCovariance N ρ ε (q.1 - q.2)|
      ≤ ∫ w : SpaceTime × SpaceTime,
        A * (|semigroupPeriodised t x w.1| * |semigroupPeriodised t x w.2| *
          (torusParabolicSize (w.1 - spaceTimeProj x) ^ (0 : ℝ) *
            torusParabolicSize (w.1 - w.2) ^ (-1 : ℝ))) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall hnn) hmaj hae
    _ = A * ∫ w : SpaceTime × SpaceTime,
          |semigroupPeriodised t x w.1| * |semigroupPeriodised t x w.2| *
            (torusParabolicSize (w.1 - spaceTimeProj x) ^ (0 : ℝ) *
              torusParabolicSize (w.1 - w.2) ^ (-1 : ℝ)) := integral_const_mul _ _
    _ ≤ A * (Cd * (t ^ (1 / 4 : ℝ)) ^ (0 + -1 : ℝ)) :=
        mul_le_mul_of_nonneg_left hdbl.2 hA
    _ = A * Cd * (t ^ (1 / 4 : ℝ)) ^ (-(1 : ℝ)) := by
        rw [zero_add]
        ring

end RegularityStructures.Phi43

end
