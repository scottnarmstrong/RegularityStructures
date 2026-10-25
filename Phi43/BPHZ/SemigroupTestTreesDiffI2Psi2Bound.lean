/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesDiffI2Psi2

/-!
# The a-priori bound (10.3) for `I(Ψ²) Ψ²`, cross-mollifier difference, semigroup test

For `0 < κ ≤ 1/16`, `0 < θ ≤ κ`, `t ∈ (0, 1]`, `lam = t^(1/4)`:
`E|∫ (F_{ρ,ε} - F_{ρ',ε'})(w) q^♯_t(x, w) dw|² ≤ C (max ε ε')^(2θ) lam^(2 (-4κ) + κ)`
(`hairerI2Psi2Field_sub_semigroupPeriodised_second_moment_le`), the same exponent `-7κ` as the
single-model bound [Hai14, (10.2)] and the gain `(max ε ε')^(2θ)` of [Hai14, (10.3)].
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **The a-priori bound (10.3) for `I(Ψ²) Ψ²`, semigroup test, cross-mollifier difference.** -/
theorem hairerI2Psi2Field_sub_semigroupPeriodised_second_moment_le (N : ℕ)
    {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {κ θ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1 / 16) (hθ : 0 < θ) (hθκ : θ ≤ κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
        ∫ ω, |∫ w, (hairerI2Psi2Field N ρ ε ξ (spaceTimeProj x) ω w -
            hairerI2Psi2Field N ρ' ε' ξ' (spaceTimeProj x) ω w) * semigroupPeriodised t x w| ^ 2 ∂P ≤
          C * (max ε ε') ^ (2 * θ) * (t ^ (1 / 4 : ℝ)) ^ (2 * (-4 * κ) + κ) := by
  have hδ : 0 < min (1 / 4 : ℝ) (7 * κ - 2 * θ) := lt_min (by norm_num) (by linarith)
  obtain ⟨C, hC, h⟩ := hairerI2Psi2Field_sub_semigroupPeriodised_second_moment_le_delta.{u} N hρ hρ'
    hθ (by linarith) hδ (min_le_left _ _)
  refine ⟨C, hC, fun {Ω _ P W ε ε' ξ ξ'} hW hε hε' hξ hξ' {t} ht ht1 x => ?_⟩
  have hmax : 0 < max ε ε' := lt_max_of_lt_left hε.1
  have hμ2 : 0 ≤ (max ε ε') ^ (2 * θ) := Real.rpow_nonneg hmax.le _
  refine (h hW hε hε' hξ hξ' ht ht1 x).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC hμ2)
  refine Real.rpow_le_rpow_of_exponent_ge (Real.rpow_pos_of_pos ht _)
    (Real.rpow_le_one ht.le ht1 (by norm_num)) ?_
  have := min_le_right (1 / 4 : ℝ) (7 * κ - 2 * θ)
  linarith

end RegularityStructures.Phi43

end
