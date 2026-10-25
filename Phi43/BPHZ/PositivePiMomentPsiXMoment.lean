/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestPsi
public import Phi43.BPHZ.ModelRegPiPsi
public import Phi43.BPHZ.SemigroupTestCoord
public import Phi43.BPHZ.PositivePiMomentField
public import Phi43.BPHZ.SemigroupTestAllMomentsSetup
public import Phi43.BPHZ.ModelRegPiMoment
import Mathlib.Tactic

/-!
# Second and `2p`-th moments of `Ψ` tested against a semigroup test profile

For a `SemigroupTestProfile` `g` at scale `lam ≤ 1`,
`E|∫ Ψ_ε g|² ≤ C lam⁻¹` uniformly in `ε ∈ (0, 1]`, the base point and `g`
(`hairerPsiField_profile_second_moment_le`).  This is `hairerPsiField_semigroupPeriodised_second_moment_le`
for an arbitrary profile instead of `q^♯_t(x, ·)`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **Second moment of `Ψ` tested against a semigroup test profile.** -/
theorem hairerPsiField_profile_second_moment_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ {x : SpaceTime} {lam B : ℝ} {Mom : ℝ → ℝ} {g : SpaceTime → ℝ},
        SemigroupTestProfile x lam B Mom g → 0 < lam →
        ∫ ω, |∫ w, hairerPsiField N ξ ω w * g w| ^ 2 ∂P ≤
          A * (semigroupTestDoubleConst B Mom 0 (-1) * lam ^ (0 + -1 : ℝ)) := by
  obtain ⟨A, hA, hQ⟩ := hairerCovariance_abs_le N ρ hρ
  refine ⟨A, hA, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ x lam B Mom g h hlam
  have := hW.isProbabilityMeasure
  have hR : Measurable (hairerCovariance N ρ ε) :=
    constantsComparison_hairerCovariance_measurable N ρ hε.1 hρ hε.2
  have hcov := hairerPsiField_integral_mul N hρ hε.1 hW hξ
  have key := secondMoment_le_integral_abs_cov (P := P) (Y := hairerPsiField N ξ)
    (measurable_hairerPsiField_uncurry N hξ) (fun u => hairerPsiField_memLp N hρ hε.1 hW hξ u)
    (M := hairerCovariance N ρ ε 0) (fun u => by rw [hcov u u, sub_self])
    (Φ := fun u v => hairerCovariance N ρ ε (u - v)) hcov h.integrable
  refine key.trans ?_
  have hdbl := h.integral_double_le (ζ := 0) (e := -1) (by norm_num) (by norm_num) hlam
  have hnn : ∀ w : SpaceTime × SpaceTime, 0 ≤ |g w.1| * |g w.2| *
      |hairerCovariance N ρ ε (w.1 - w.2)| := fun w =>
    mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)
  have hmaj : Integrable (fun w : SpaceTime × SpaceTime =>
      A * (|g w.1| * |g w.2| *
        (torusParabolicSize (w.1 - x) ^ (0 : ℝ) * torusParabolicSize (w.1 - w.2) ^ (-1 : ℝ)))) :=
    hdbl.1.const_mul A
  have hae : ∀ᵐ w : SpaceTime × SpaceTime ∂volume,
      |g w.1| * |g w.2| * |hairerCovariance N ρ ε (w.1 - w.2)| ≤
      A * (|g w.1| * |g w.2| *
        (torusParabolicSize (w.1 - x) ^ (0 : ℝ) * torusParabolicSize (w.1 - w.2) ^ (-1 : ℝ))) := by
    filter_upwards [SemigroupTestProfile.ae_pos_pair x] with w hw
    have hq := hQ hε.1 hε.2 (w.1 - w.2) hw.2
    have hgg : 0 ≤ |g w.1| * |g w.2| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
    rw [Real.rpow_zero, one_mul, Real.rpow_neg_one]
    rw [Real.rpow_neg_one] at hq
    calc _ ≤ |g w.1| * |g w.2| * (A * (torusParabolicSize (w.1 - w.2))⁻¹) :=
          mul_le_mul_of_nonneg_left hq hgg
      _ = _ := by ring
  calc ∫ q : SpaceTime × SpaceTime, |g q.1| * |g q.2| * |hairerCovariance N ρ ε (q.1 - q.2)|
      ≤ ∫ w : SpaceTime × SpaceTime,
        A * (|g w.1| * |g w.2| *
          (torusParabolicSize (w.1 - x) ^ (0 : ℝ) * torusParabolicSize (w.1 - w.2) ^ (-1 : ℝ))) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall hnn) hmaj hae
    _ = A * ∫ w : SpaceTime × SpaceTime, |g w.1| * |g w.2| *
          (torusParabolicSize (w.1 - x) ^ (0 : ℝ) * torusParabolicSize (w.1 - w.2) ^ (-1 : ℝ)) :=
        integral_const_mul _ _
    _ ≤ A * (semigroupTestDoubleConst B Mom 0 (-1) * lam ^ (0 + -1 : ℝ)) :=
        mul_le_mul_of_nonneg_left (by simpa using hdbl.2) hA

/-- **Moments of `Ψ` tested against a profile, all `p`.** -/
theorem hairerPsiField_profile_integrable_pow_le (p : ℕ) (hp : 1 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ}
      {ξ : Ω → SpaceTime → ℝ} (N : ℕ), IsMollifier ρ → IsWhiteNoise P W → 0 < ε →
      IsRegularisedNoise P W ρ ε ξ → ∀ {g : SpaceTime → ℝ}, Measurable g → Integrable g →
        Integrable (fun ω => (∫ w, hairerPsiField N ξ ω w * g w) ^ (2 * p)) P ∧
        ∫ ω, (∫ w, hairerPsiField N ξ ω w * g w) ^ (2 * p) ∂P ≤
          A * (∫ ω, (∫ w, hairerPsiField N ξ ω w * g w) ^ 2 ∂P) ^ p := by
  obtain ⟨A, hA0, hA⟩ :=
    integrable_and_integral_pow_two_mul_le_of_polyIntegral_timeTruncation.{u} 1 p hp
  refine ⟨A, hA0, fun {Ω _ P W ρ ε ξ} N hρ hW hε hξ {g} hgm hgi => ?_⟩
  have h := hA hW (continuous_hairerPsiField N hξ.1) (measurable_hairerPsiField_apply N hξ)
    (exists_hairerPsiField_pairing N hρ hε hW hξ) (integral_hairerPsiField_sq_le N hρ hε hW hξ)
    hgm hgi Polynomial.X (by simp)
  simpa only [Polynomial.eval_X] using h

end RegularityStructures.Phi43

end
