/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestWickCov
public import Phi43.BPHZ.TreeWickCube
public import Phi43.BPHZ.TreeWickSquare

/-!
# Second moments of the Wick powers of `Ψ` tested against the periodised semigroup kernel

For `lam = t^(1/4)`, `t ∈ (0, 1]`, `ε ∈ (0, 1]` and every `x`,

* `E|∫ :Ψ²:_ε q^♯_t(x, ·)|² ≤ C lam⁻²` (`hairerPsiWickSquare_semigroupPeriodised_second_moment_le`),
* `E|∫ :Ψ³:_ε q^♯_t(x, ·)|² ≤ C lam⁻³` (`hairerPsiWickCube_semigroupPeriodised_second_moment_le`),

with `C` independent of `ε`, `t` and `x`.  The covariances are `2 Q_ε²` and `6 Q_ε³`, and
`|Q_ε(z)| ≤ A s(z)⁻¹` globally (`hairerCovariance_abs_le`), so
`exists_semigroupPeriodised_second_moment_le_cov` applies with `e = -2`, `-3`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem rpow_neg_one_pow {s : ℝ} (hs : 0 < s) (n : ℕ) :
    (s ^ (-(1 : ℝ))) ^ n = s ^ (-(n : ℝ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
  congr 1
  ring

private theorem abs_pow_le_of_abs_le {R A s : ℝ} (hs : 0 < s) (hR : |R| ≤ A * s ^ (-(1 : ℝ)))
    (n : ℕ) : |R ^ n| ≤ A ^ n * s ^ (-(n : ℝ)) := by
  rw [abs_pow, ← rpow_neg_one_pow hs n, ← mul_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) hR n

/-- **Second moment of the tested Wick square `:Ψ²:`, semigroup test.** -/
theorem hairerPsiWickSquare_semigroupPeriodised_second_moment_le (N : ℕ)
    {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
        ∫ ω, |∫ w, hairerPsiWickSquare N ρ ε ξ ω w * semigroupPeriodised t x w| ^ 2 ∂P ≤
          C * (t ^ (1 / 4 : ℝ)) ^ (-(2 : ℝ)) := by
  obtain ⟨A, hA, hQ⟩ := hairerCovariance_abs_le N ρ hρ
  obtain ⟨Cd, hCd0, hCd⟩ := exists_semigroupPeriodised_second_moment_le_cov.{u} (e := -2)
    (by norm_num)
  refine ⟨Cd * (2 * A ^ 2), mul_nonneg hCd0 (by positivity), ?_⟩
  intro Ω _ P W ε ξ hW hε hξ t ht ht1 x
  have := hW.isProbabilityMeasure
  have hcov := hairerPsiWickSquare_integral_mul N hρ hε.1 hW hξ
  have h := hCd (P := P) (measurable_hairerPsiWickSquare_uncurry N hξ)
    (fun u => hairerPsiWickSquare_memLp N hρ hε.1 hW hξ u)
    (M := 2 * hairerCovariance N ρ ε 0 ^ 2) (fun u => by rw [hcov u u, sub_self])
    (Φ := fun u v => 2 * hairerCovariance N ρ ε (u - v) ^ 2) hcov (A := 2 * A ^ 2)
    (by positivity) (fun u v hs => by
      have h1 := abs_pow_le_of_abs_le hs (hQ hε.1 hε.2 (u - v) hs) 2
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      push_cast at h1
      calc 2 * |hairerCovariance N ρ ε (u - v) ^ 2| ≤
          2 * (A ^ 2 * torusParabolicSize (u - v) ^ (-(2 : ℝ))) :=
            mul_le_mul_of_nonneg_left h1 (by norm_num)
        _ = _ := by ring) ht ht1 x
  simpa only [mul_assoc, mul_comm (2 * A ^ 2)] using h

/-- **Second moment of the tested Wick cube `:Ψ³:`, semigroup test.** -/
theorem hairerPsiWickCube_semigroupPeriodised_second_moment_le (N : ℕ)
    {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
        ∫ ω, |∫ w, hairerPsiWickCube N ρ ε ξ ω w * semigroupPeriodised t x w| ^ 2 ∂P ≤
          C * (t ^ (1 / 4 : ℝ)) ^ (-(3 : ℝ)) := by
  obtain ⟨A, hA, hQ⟩ := hairerCovariance_abs_le N ρ hρ
  obtain ⟨Cd, hCd0, hCd⟩ := exists_semigroupPeriodised_second_moment_le_cov.{u} (e := -3)
    (by norm_num)
  refine ⟨Cd * (6 * A ^ 3), mul_nonneg hCd0 (by positivity), ?_⟩
  intro Ω _ P W ε ξ hW hε hξ t ht ht1 x
  have := hW.isProbabilityMeasure
  have hcov := hairerPsiWickCube_integral_mul N hρ hε.1 hW hξ
  have h := hCd (P := P) (measurable_hairerPsiWickCube_uncurry N hξ)
    (fun u => hairerPsiWickCube_memLp N hρ hε.1 hW hξ u)
    (M := 6 * hairerCovariance N ρ ε 0 ^ 3) (fun u => by rw [hcov u u, sub_self])
    (Φ := fun u v => 6 * hairerCovariance N ρ ε (u - v) ^ 3) hcov (A := 6 * A ^ 3)
    (by positivity) (fun u v hs => by
      have h1 := abs_pow_le_of_abs_le hs (hQ hε.1 hε.2 (u - v) hs) 3
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
      push_cast at h1
      calc 6 * |hairerCovariance N ρ ε (u - v) ^ 3| ≤
          6 * (A ^ 3 * torusParabolicSize (u - v) ^ (-(3 : ℝ))) :=
            mul_le_mul_of_nonneg_left h1 (by norm_num)
        _ = _ := by ring) ht ht1 x
  simpa only [mul_assoc, mul_comm (6 * A ^ 3)] using h

end RegularityStructures.Phi43

end
