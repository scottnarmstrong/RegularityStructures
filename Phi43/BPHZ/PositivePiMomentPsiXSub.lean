/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.PositivePiMomentPsiXMoment
public import Phi43.BPHZ.CrossMollifierDifference
public import Phi43.BPHZ.CrossMollifierPsi
public import Phi43.Stochastic.WhiteNoiseL2
import Mathlib.Tactic

/-!
# Two-scale differences of `Ψ` tested against a semigroup test profile

For regularised noises `ξ` (mollifier `ρ`, scale `ε`), `ξ'` (mollifier `ρ'`, scale `ε'`) driven by the
same white noise and a `SemigroupTestProfile` `g` at scale `lam ≤ 1`:

* `hairerPsiField_profile_sub_second_moment_le`:
  `E|∫ (Ψ - Ψ') g|² ≤ C (ε ∨ ε')^(2θ) lam^(-1-2θ)`;
* `hairerPsiField_profile_sub_integrable_pow_le`: all moments of `∫ (Ψ - Ψ') g`.

The difference `Ψ - Ψ'` is itself a continuous Gaussian field of the same type
(`exists_hairerPsiField_sub_pairing`), so the moment equivalence applies to it directly.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
  {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ}

/-- `Ψ - Ψ'` is a white-noise pairing. -/
theorem exists_hairerPsiField_sub_pairing (N : ℕ) (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ')
    (hε : 0 < ε) (hε' : 0 < ε') (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ)
    (hξ' : IsRegularisedNoise P W ρ' ε' ξ') (y : SpaceTime) :
    ∃ h : SpaceTime → ℝ, MemLp h 2 ∧
      (fun ω => hairerPsiField N ξ ω y - hairerPsiField N ξ' ω y) =ᵐ[P] W h := by
  obtain ⟨h₁, hm₁, he₁⟩ := exists_hairerPsiField_pairing N hρ hε hW hξ y
  obtain ⟨h₂, hm₂, he₂⟩ := exists_hairerPsiField_pairing N hρ' hε' hW hξ' y
  refine ⟨h₁ - h₂, hm₁.sub hm₂, ?_⟩
  filter_upwards [he₁, he₂, whiteNoise_pairing_sub_ae hW hm₁ hm₂] with ω h1 h2 h3
  rw [h1, h2, h3]

/-- The second moment of `Ψ - Ψ'` at a point is bounded. -/
theorem integral_hairerPsiField_sub_sq_le (N : ℕ) (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ')
    (hε : 0 < ε) (hε' : 0 < ε') (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ)
    (hξ' : IsRegularisedNoise P W ρ' ε' ξ') (y : SpaceTime) :
    ∫ ω, (hairerPsiField N ξ ω y - hairerPsiField N ξ' ω y) ^ 2 ∂P ≤
      4 * max (hairerCovariance N ρ ε 0) (hairerCovariance N ρ' ε' 0) := by
  have := hW.isProbabilityMeasure
  have h1 := integral_hairerPsiField_sq_le N hρ hε hW hξ y
  have h2 := integral_hairerPsiField_sq_le N hρ' hε' hW hξ' y
  have m1 := hairerPsiField_memLp N hρ hε hW hξ y
  have m2 := hairerPsiField_memLp N hρ' hε' hW hξ' y
  have i1 : Integrable (fun ω => hairerPsiField N ξ ω y ^ 2) P := m1.integrable_sq
  have i2 : Integrable (fun ω => hairerPsiField N ξ' ω y ^ 2) P := m2.integrable_sq
  have i12 : Integrable (fun ω => (hairerPsiField N ξ ω y - hairerPsiField N ξ' ω y) ^ 2) P :=
    (m1.sub m2).integrable_sq
  calc ∫ ω, (hairerPsiField N ξ ω y - hairerPsiField N ξ' ω y) ^ 2 ∂P
      ≤ ∫ ω, (2 * hairerPsiField N ξ ω y ^ 2 + 2 * hairerPsiField N ξ' ω y ^ 2) ∂P := by
        refine integral_mono i12 ((i1.const_mul 2).add (i2.const_mul 2)) fun ω => ?_
        nlinarith [sq_nonneg (hairerPsiField N ξ ω y + hairerPsiField N ξ' ω y)]
    _ = 2 * ∫ ω, hairerPsiField N ξ ω y ^ 2 ∂P + 2 * ∫ ω, hairerPsiField N ξ' ω y ^ 2 ∂P := by
        rw [integral_add (i1.const_mul 2) (i2.const_mul 2), integral_const_mul, integral_const_mul]
    _ ≤ 4 * max (hairerCovariance N ρ ε 0) (hairerCovariance N ρ' ε' 0) := by
        have := le_max_left (hairerCovariance N ρ ε 0) (hairerCovariance N ρ' ε' 0)
        have := le_max_right (hairerCovariance N ρ ε 0) (hairerCovariance N ρ' ε' 0)
        linarith

end RegularityStructures.Phi43

end

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **All moments of `∫ (Ψ - Ψ') g`.** -/
theorem hairerPsiField_profile_sub_integrable_pow_le (p : ℕ) (hp : 1 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {ε ε' : ℝ}
      {ξ ξ' : Ω → SpaceTime → ℝ} (N : ℕ), IsMollifier ρ → IsMollifier ρ' → IsWhiteNoise P W →
      0 < ε → 0 < ε' → IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ {g : SpaceTime → ℝ}, Measurable g → Integrable g →
        Integrable (fun ω => (∫ w, (hairerPsiField N ξ ω w - hairerPsiField N ξ' ω w) * g w) ^
          (2 * p)) P ∧
        ∫ ω, (∫ w, (hairerPsiField N ξ ω w - hairerPsiField N ξ' ω w) * g w) ^ (2 * p) ∂P ≤
          A * (∫ ω, (∫ w, (hairerPsiField N ξ ω w - hairerPsiField N ξ' ω w) * g w) ^ 2 ∂P) ^ p := by
  obtain ⟨A, hA0, hA⟩ :=
    integrable_and_integral_pow_two_mul_le_of_polyIntegral_timeTruncation.{u} 1 p hp
  refine ⟨A, hA0, fun {Ω _ P W ρ ρ' ε ε' ξ ξ'} N hρ hρ' hW hε hε' hξ hξ' {g} hgm hgi => ?_⟩
  have h := hA hW (ψ := fun ω y => hairerPsiField N ξ ω y - hairerPsiField N ξ' ω y)
    (fun ω => (continuous_hairerPsiField N hξ.1 ω).sub (continuous_hairerPsiField N hξ'.1 ω))
    (fun y => (measurable_hairerPsiField_apply N hξ y).sub (measurable_hairerPsiField_apply N hξ' y))
    (exists_hairerPsiField_sub_pairing N hρ hρ' hε hε' hW hξ hξ')
    (integral_hairerPsiField_sub_sq_le N hρ hρ' hε hε' hW hξ hξ') hgm hgi Polynomial.X (by simp)
  simpa only [Polynomial.eval_X] using h

/-- **Second moment of `∫ (Ψ - Ψ') g` for a semigroup test profile.** -/
theorem hairerPsiField_profile_sub_second_moment_le (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ {x : SpaceTime} {lam B : ℝ} {Mom : ℝ → ℝ} {g : SpaceTime → ℝ},
        SemigroupTestProfile x lam B Mom g → 0 < lam →
        ∫ ω, |∫ w, (hairerPsiField N ξ ω w - hairerPsiField N ξ' ω w) * g w| ^ 2 ∂P ≤
          A * (max ε ε') ^ (2 * θ) *
            (semigroupTestDoubleConst B Mom 0 (-1 - 2 * θ) * lam ^ (0 + (-1 - 2 * θ) : ℝ)) := by
  obtain ⟨CQ, hCQ, hQ⟩ := hairerKernelDiffCovarianceTwo_abs_le N ρ ρ' hρ hρ' hθ hθ1
  refine ⟨CQ, hCQ, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' x lam B Mom g h hlam
  have := hW.isProbabilityMeasure
  have hMx : 0 ≤ (max ε ε') ^ (2 * θ) := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
  have hcov := hairerPsiField_sub_integral_mulTwo N hρ hρ' hε.1 hε'.1 hW hξ hξ'
  have key := secondMoment_le_integral_abs_cov (P := P)
    (Y := fun ω u => hairerPsiField N ξ ω u - hairerPsiField N ξ' ω u)
    ((measurable_hairerPsiField_uncurry N hξ).sub (measurable_hairerPsiField_uncurry N hξ'))
    (fun u => (hairerPsiField_memLp N hρ hε.1 hW hξ u).sub
      (hairerPsiField_memLp N hρ' hε'.1 hW hξ' u))
    (M := hairerKernelDiffCovarianceTwo N ρ ε ρ' ε' 0)
    (fun u => by rw [hcov u u, sub_self])
    (Φ := fun u v => hairerKernelDiffCovarianceTwo N ρ ε ρ' ε' (u - v)) hcov h.integrable
  refine key.trans ?_
  have hdbl := h.integral_double_le (ζ := 0) (e := -1 - 2 * θ) (by norm_num) (by linarith) hlam
  set K : ℝ := CQ * (max ε ε') ^ (2 * θ) with hK
  have hK0 : 0 ≤ K := mul_nonneg hCQ hMx
  have hnn : ∀ w : SpaceTime × SpaceTime, 0 ≤ |g w.1| * |g w.2| *
      |hairerKernelDiffCovarianceTwo N ρ ε ρ' ε' (w.1 - w.2)| := fun w =>
    mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)
  have hmaj : Integrable (fun w : SpaceTime × SpaceTime =>
      K * (|g w.1| * |g w.2| *
        (torusParabolicSize (w.1 - x) ^ (0 : ℝ) *
          torusParabolicSize (w.1 - w.2) ^ (-1 - 2 * θ : ℝ)))) := hdbl.1.const_mul K
  have hae : ∀ᵐ w : SpaceTime × SpaceTime ∂volume,
      |g w.1| * |g w.2| * |hairerKernelDiffCovarianceTwo N ρ ε ρ' ε' (w.1 - w.2)| ≤
      K * (|g w.1| * |g w.2| *
        (torusParabolicSize (w.1 - x) ^ (0 : ℝ) *
          torusParabolicSize (w.1 - w.2) ^ (-1 - 2 * θ : ℝ))) := by
    filter_upwards [SemigroupTestProfile.ae_pos_pair x] with w hw
    have hq := hQ hε.1 hε.2 hε'.1 hε'.2 (w.1 - w.2) hw.2
    have hgg : 0 ≤ |g w.1| * |g w.2| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
    rw [Real.rpow_zero, one_mul]
    calc _ ≤ |g w.1| * |g w.2| * (K * torusParabolicSize (w.1 - w.2) ^ (-1 - 2 * θ : ℝ)) :=
          mul_le_mul_of_nonneg_left hq hgg
      _ = _ := by ring
  calc ∫ q : SpaceTime × SpaceTime, |g q.1| * |g q.2| *
        |hairerKernelDiffCovarianceTwo N ρ ε ρ' ε' (q.1 - q.2)|
      ≤ ∫ w : SpaceTime × SpaceTime,
        K * (|g w.1| * |g w.2| *
          (torusParabolicSize (w.1 - x) ^ (0 : ℝ) *
            torusParabolicSize (w.1 - w.2) ^ (-1 - 2 * θ : ℝ))) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall hnn) hmaj hae
    _ = K * ∫ w : SpaceTime × SpaceTime, |g w.1| * |g w.2| *
          (torusParabolicSize (w.1 - x) ^ (0 : ℝ) *
            torusParabolicSize (w.1 - w.2) ^ (-1 - 2 * θ : ℝ)) := integral_const_mul _ _
    _ ≤ K * (semigroupTestDoubleConst B Mom 0 (-1 - 2 * θ) * lam ^ (0 + (-1 - 2 * θ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hdbl.2 hK0
    _ = _ := by rw [hK]

end RegularityStructures.Phi43

end
