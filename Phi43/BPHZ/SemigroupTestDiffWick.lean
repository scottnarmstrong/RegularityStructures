/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestWickCov
public import Phi43.BPHZ.GammaMomentCrossCov
public import Phi43.BPHZ.CrossMollifierDifference

/-!
# Second moments of the cross-mollifier differences of the Wick powers of `Ψ`, semigroup test

For `θ ∈ (0, 1]` (square), `θ ∈ (0, 1/2]` (cube), `t ∈ (0, 1]`, `lam = t^(1/4)` and every `x`,

* `E|∫ (:Ψ²:_{ρ,ε} - :Ψ²:_{ρ',ε'}) q^♯_t(x, ·)|² ≤ C (max ε ε')^(2θ) lam^(-(2+2θ))`,
* `E|∫ (:Ψ³:_{ρ,ε} - :Ψ³:_{ρ',ε'}) q^♯_t(x, ·)|² ≤ C (max ε ε')^(2θ) lam^(-(3+2θ))`.

The covariances are `2(a² - b² - c² + d²)` and `6(a³ - b³ - c³ + d³)`
(`hairerPsiWickSquare_sub_integral_mulTwo`, `hairerPsiWickCube_sub_integral_mulTwo`) and the second
differences of the cross covariances satisfy the global bounds
`hairerCrossTwo_sq_sub_abs_le`, `hairerCrossTwo_cube_sub_abs_le`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **Second moment of the tested cross-mollifier difference of `:Ψ²:`, semigroup test.** -/
theorem hairerPsiWickSquare_sub_semigroupPeriodised_second_moment_le (N : ℕ)
    {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ')
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
        ∫ ω, |∫ w, (hairerPsiWickSquare N ρ ε ξ ω w - hairerPsiWickSquare N ρ' ε' ξ' ω w) *
            semigroupPeriodised t x w| ^ 2 ∂P ≤
          C * (max ε ε') ^ (2 * θ) * (t ^ (1 / 4 : ℝ)) ^ (-(2 + 2 * θ)) := by
  obtain ⟨A, hA, hQ⟩ := hairerCrossTwo_sq_sub_abs_le N ρ ρ' hρ hρ' hθ hθ1
  obtain ⟨Cd, hCd0, hCd⟩ := exists_semigroupPeriodised_second_moment_le_cov.{u}
    (e := -(2 + 2 * θ)) (by linarith)
  refine ⟨Cd * (2 * A), mul_nonneg hCd0 (by positivity), ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' t ht ht1 x
  have := hW.isProbabilityMeasure
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
        _ = _ := by ring) ht ht1 x
  refine h.trans (le_of_eq ?_)
  ring

/-- **Second moment of the tested cross-mollifier difference of `:Ψ³:`, semigroup test.** -/
theorem hairerPsiWickCube_sub_semigroupPeriodised_second_moment_le (N : ℕ)
    {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ')
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
        ∫ ω, |∫ w, (hairerPsiWickCube N ρ ε ξ ω w - hairerPsiWickCube N ρ' ε' ξ' ω w) *
            semigroupPeriodised t x w| ^ 2 ∂P ≤
          C * (max ε ε') ^ (2 * θ) * (t ^ (1 / 4 : ℝ)) ^ (-(3 + 2 * θ)) := by
  obtain ⟨A, hA, hQ⟩ := hairerCrossTwo_cube_sub_abs_le N ρ ρ' hρ hρ' hθ (by linarith)
  obtain ⟨Cd, hCd0, hCd⟩ := exists_semigroupPeriodised_second_moment_le_cov.{u}
    (e := -(3 + 2 * θ)) (by linarith)
  refine ⟨Cd * (6 * A), mul_nonneg hCd0 (by positivity), ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' t ht ht1 x
  have := hW.isProbabilityMeasure
  have hM0 : 0 ≤ (max ε ε') ^ (2 * θ) := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
  have hcov := hairerPsiWickCube_sub_integral_mulTwo N hρ hρ' hε.1 hε'.1 hW hξ hξ'
  have h := hCd (P := P)
    ((measurable_hairerPsiWickCube_uncurry N hξ).sub
      (measurable_hairerPsiWickCube_uncurry N hξ'))
    (fun u => hairerPsiWickCube_sub_memLpTwo N hρ hρ' hε.1 hε'.1 hW hξ hξ' u)
    (M := 6 * (hairerCrossCovarianceTwo N ρ ε ρ ε 0 ^ 3 -
      hairerCrossCovarianceTwo N ρ ε ρ' ε' 0 ^ 3 -
      hairerCrossCovarianceTwo N ρ' ε' ρ ε 0 ^ 3 + hairerCrossCovarianceTwo N ρ' ε' ρ' ε' 0 ^ 3))
    (fun u => by
      have := hcov u u
      rw [sub_self] at this
      exact this.le)
    (Φ := fun u v => 6 * (hairerCrossCovarianceTwo N ρ ε ρ ε (u - v) ^ 3 -
      hairerCrossCovarianceTwo N ρ ε ρ' ε' (u - v) ^ 3 -
      hairerCrossCovarianceTwo N ρ' ε' ρ ε (u - v) ^ 3 +
      hairerCrossCovarianceTwo N ρ' ε' ρ' ε' (u - v) ^ 3)) hcov
    (A := 6 * (A * (max ε ε') ^ (2 * θ))) (by positivity) (fun u v hs => by
      have h0 := hQ hε.1 hε.2 hε'.1 hε'.2 (u - v) hs
      rw [show -3 - 2 * θ = -(3 + 2 * θ) by ring] at h0
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
      calc 6 * _ ≤ 6 * (A * (max ε ε') ^ (2 * θ) * torusParabolicSize (u - v) ^ (-(3 + 2 * θ))) :=
            mul_le_mul_of_nonneg_left h0 (by norm_num)
        _ = _ := by ring) ht ht1 x
  refine h.trans (le_of_eq ?_)
  ring

end RegularityStructures.Phi43

end
