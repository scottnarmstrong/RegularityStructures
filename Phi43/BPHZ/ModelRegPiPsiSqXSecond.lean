/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ModelRegPiPsiSqXCov

/-!
# Second moments of the Wick square tested against the coordinate-weighted kernel

With `g_i = semigroupPeriodisedX t x i` (the periodisation of `Q_t(x, y)(yᵢ - xᵢ)`), `t ∈ (0, 1]`
and `lam = t^(1/4)`:

* `E|∫ :Ψ²:_ε g_i|² ≤ C` (`hairerPsiWickSquare_semigroupPeriodisedX_second_moment_le`);
* `E|∫ (:Ψ²:_ε - :Ψ²:_ε') g_i|² ≤ C (max ε ε')^(2θ) lam^(-2θ)`
  (`hairerPsiWickSquare_sub_semigroupPeriodisedX_second_moment_le`).
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem abs_pow_le_of_abs_le' {R A s : ℝ} (hs : 0 < s) (hR : |R| ≤ A * s ^ (-(1 : ℝ)))
    (n : ℕ) : |R ^ n| ≤ A ^ n * s ^ (-(n : ℝ)) := by
  rw [abs_pow]
  calc |R| ^ n ≤ (A * s ^ (-(1 : ℝ))) ^ n := pow_le_pow_left₀ (abs_nonneg _) hR n
    _ = A ^ n * (s ^ (-(1 : ℝ))) ^ n := mul_pow _ _ _
    _ = _ := by
      rw [← Real.rpow_natCast (s ^ (-(1 : ℝ))) n, ← Real.rpow_mul hs.le]
      congr 2
      ring

/-- **Second moment of the Wick square tested against `g_i`.** -/
theorem hairerPsiWickSquare_semigroupPeriodisedX_second_moment_le (N : ℕ)
    {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ) (i : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
        ∫ ω, |∫ w, hairerPsiWickSquare N ρ ε ξ ω w * semigroupPeriodisedX t x i w| ^ 2 ∂P ≤ C := by
  obtain ⟨A, hA, hQ⟩ := hairerCovariance_abs_le N ρ hρ
  obtain ⟨B, hB0, hB⟩ := exists_semigroupTestProfile_semigroupPeriodisedX i
  obtain ⟨Cd, hCd0, hCd⟩ := second_moment_le_cov_of_profile.{u} (e := -2) (by norm_num) B
    (fun r => parabolicMomentConst (r + 1))
  refine ⟨Cd * (2 * A ^ 2), mul_nonneg hCd0 (by positivity), ?_⟩
  intro Ω _ P W ε ξ hW hε hξ t ht ht1 x
  have := hW.isProbabilityMeasure
  have hlam : 0 < t ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos ht _
  have hcov := hairerPsiWickSquare_integral_mul N hρ hε.1 hW hξ
  have h := hCd (P := P) (measurable_hairerPsiWickSquare_uncurry N hξ)
    (fun u => hairerPsiWickSquare_memLp N hρ hε.1 hW hξ u)
    (M := 2 * hairerCovariance N ρ ε 0 ^ 2) (fun u => by rw [hcov u u, sub_self])
    (Φ := fun u v => 2 * hairerCovariance N ρ ε (u - v) ^ 2) hcov (A := 2 * A ^ 2)
    (by positivity) (fun u v hs => by
      have h1 := abs_pow_le_of_abs_le' hs (hQ hε.1 hε.2 (u - v) hs) 2
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      push_cast at h1
      calc 2 * |hairerCovariance N ρ ε (u - v) ^ 2| ≤
          2 * (A ^ 2 * torusParabolicSize (u - v) ^ (-(2 : ℝ))) :=
            mul_le_mul_of_nonneg_left h1 (by norm_num)
        _ = _ := by ring) (hB ht ht1 x) hlam
  rw [integral_sq_tested_scale (P := P) _ _ hlam.ne']
  calc (t ^ (1 / 4 : ℝ)) ^ 2 * ∫ ω, |∫ w, hairerPsiWickSquare N ρ ε ξ ω w *
        ((t ^ (1 / 4 : ℝ))⁻¹ * semigroupPeriodisedX t x i w)| ^ 2 ∂P
      ≤ (t ^ (1 / 4 : ℝ)) ^ 2 * (Cd * (2 * A ^ 2) * (t ^ (1 / 4 : ℝ)) ^ (-2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (by simpa [mul_assoc] using h) (by positivity)
    _ = Cd * (2 * A ^ 2) * ((t ^ (1 / 4 : ℝ)) ^ 2 * (t ^ (1 / 4 : ℝ)) ^ (-2 : ℝ)) := by ring
    _ = Cd * (2 * A ^ 2) := by
        rw [sq_mul_rpow_eq_rpow_add hlam]
        norm_num

/-- **Second moment of the tested cross-mollifier difference of `:Ψ²:` against `g_i`.** -/
theorem hairerPsiWickSquare_sub_semigroupPeriodisedX_second_moment_le (N : ℕ)
    {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ')
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (i : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
        ∫ ω, |∫ w, (hairerPsiWickSquare N ρ ε ξ ω w - hairerPsiWickSquare N ρ' ε' ξ' ω w) *
            semigroupPeriodisedX t x i w| ^ 2 ∂P ≤
          C * (max ε ε') ^ (2 * θ) * (t ^ (1 / 4 : ℝ)) ^ (-(2 * θ)) := by
  obtain ⟨A, hA, hQ⟩ := hairerCrossTwo_sq_sub_abs_le N ρ ρ' hρ hρ' hθ hθ1
  obtain ⟨B, hB0, hB⟩ := exists_semigroupTestProfile_semigroupPeriodisedX i
  obtain ⟨Cd, hCd0, hCd⟩ := second_moment_le_cov_of_profile.{u} (e := -(2 + 2 * θ))
    (by linarith) B (fun r => parabolicMomentConst (r + 1))
  refine ⟨Cd * (2 * A), mul_nonneg hCd0 (by positivity), ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' t ht ht1 x
  have := hW.isProbabilityMeasure
  have hlam : 0 < t ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos ht _
  have hM0 : 0 ≤ (max ε ε') ^ (2 * θ) := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
  have hcov := hairerPsiWickSquare_sub_integral_mulTwo N hρ hρ' hε.1 hε'.1 hW hξ hξ'
  have h := hCd (P := P)
    ((measurable_hairerPsiWickSquare_uncurry N hξ).sub
      (measurable_hairerPsiWickSquare_uncurry N hξ'))
    (fun u => hairerPsiWickSquare_sub_memLpTwo N hρ hρ' hε.1 hε'.1 hW hξ hξ' u)
    (M := 2 * (hairerCrossCovarianceTwo N ρ ε ρ ε 0 ^ 2 -
      hairerCrossCovarianceTwo N ρ ε ρ' ε' 0 ^ 2 -
      hairerCrossCovarianceTwo N ρ' ε' ρ ε 0 ^ 2 + hairerCrossCovarianceTwo N ρ' ε' ρ' ε' 0 ^ 2))
    (fun u => by
      have := hcov u u
      rw [sub_self] at this
      exact this.le)
    (Φ := fun u v => 2 * (hairerCrossCovarianceTwo N ρ ε ρ ε (u - v) ^ 2 -
      hairerCrossCovarianceTwo N ρ ε ρ' ε' (u - v) ^ 2 -
      hairerCrossCovarianceTwo N ρ' ε' ρ ε (u - v) ^ 2 +
      hairerCrossCovarianceTwo N ρ' ε' ρ' ε' (u - v) ^ 2)) hcov
    (A := 2 * (A * (max ε ε') ^ (2 * θ))) (by positivity) (fun u v hs => by
      have h0 := hQ hε.1 hε.2 hε'.1 hε'.2 (u - v) hs
      rw [show -2 - 2 * θ = -(2 + 2 * θ) by ring] at h0
      rw [abs_mul, abs_two]
      calc 2 * _ ≤ 2 * (A * (max ε ε') ^ (2 * θ) * torusParabolicSize (u - v) ^ (-(2 + 2 * θ))) :=
            mul_le_mul_of_nonneg_left h0 (by norm_num)
        _ = _ := by ring) (hB ht ht1 x) hlam
  rw [integral_sq_tested_scale (P := P) _ _ hlam.ne']
  calc (t ^ (1 / 4 : ℝ)) ^ 2 * ∫ ω, |∫ w, (hairerPsiWickSquare N ρ ε ξ ω w -
        hairerPsiWickSquare N ρ' ε' ξ' ω w) *
        ((t ^ (1 / 4 : ℝ))⁻¹ * semigroupPeriodisedX t x i w)| ^ 2 ∂P
      ≤ (t ^ (1 / 4 : ℝ)) ^ 2 * (Cd * (2 * (A * (max ε ε') ^ (2 * θ))) *
          (t ^ (1 / 4 : ℝ)) ^ (-(2 + 2 * θ))) :=
        mul_le_mul_of_nonneg_left (by simpa [mul_assoc] using h) (by positivity)
    _ = Cd * (2 * A) * (max ε ε') ^ (2 * θ) *
          ((t ^ (1 / 4 : ℝ)) ^ 2 * (t ^ (1 / 4 : ℝ)) ^ (-(2 + 2 * θ))) := by ring
    _ = _ := by
        rw [sq_mul_rpow_eq_rpow_add hlam]
        congr 2
        ring

end RegularityStructures.Phi43

end
