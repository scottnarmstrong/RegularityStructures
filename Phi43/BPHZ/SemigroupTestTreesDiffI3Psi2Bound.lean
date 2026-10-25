/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesDiffI3Psi2

/-!
# The difference bound (10.3) for `I(Ψ³)Ψ²` against the periodised semigroup kernel

For `0 < κ ≤ 1/16` and `0 < θ ≤ κ`, uniformly in `ε, ε' ∈ (0, 1]`, `t ∈ (0, 1]` and `x`,
`E|∫ (F_{ρ,ε} - F_{ρ',ε'})(proj x) q^♯_t(x, ·)|² ≤ C (max ε ε')^(2θ) (t^(1/4))^(-1 - 9κ)`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **The difference bound (10.3) for `I(Ψ³)Ψ²`, semigroup test**: for two mollifiers `ρ`, `ρ'`
and two regularisations of the same white noise,
`E|∫ (F_{ρ,ε} - F_{ρ',ε'})(proj x) q^♯_t(x, ·)|² ≤ C (max ε ε')^(2θ) (t^(1/4))^(-1 - 9κ)`. -/
theorem hairerI3Psi2Field_sub_semigroupPeriodised_second_moment_le (N : ℕ)
    {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {κ θ : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1 / 16) (hθ : 0 < θ) (hθκ : θ ≤ κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
        ∫ ω, |∫ w, (hairerI3Psi2Field N ρ ε ξ (spaceTimeProj x) ω w -
            hairerI3Psi2Field N ρ' ε' ξ' (spaceTimeProj x) ω w) * semigroupPeriodised t x w| ^ 2
          ∂P ≤ C * (max ε ε') ^ (2 * θ) * (t ^ (1 / 4 : ℝ)) ^ (-1 - 9 * κ) := by
  have hδ : 0 < min (1 / 8 : ℝ) (7 * κ / 2) := lt_min (by norm_num) (by linarith)
  obtain ⟨C, hC, h⟩ := hairerI3Psi2Field_sub_semigroupPeriodised_second_moment_le_delta.{u} N hρ
    hρ' (θ := θ) (δ := min (1 / 8 : ℝ) (7 * κ / 2)) hθ (by linarith) hδ (min_le_left _ _)
  refine ⟨C, hC, fun {Ω _ P W ε ε' ξ ξ'} hW hε hε' hξ hξ' {t} ht ht1 x => ?_⟩
  refine (h hW hε hε' hξ hξ' ht ht1 x).trans ?_
  have hm : 0 ≤ C * (max ε ε') ^ (2 * θ) :=
    mul_nonneg hC (Real.rpow_nonneg (le_max_of_le_left hε.1.le) _)
  refine mul_le_mul_of_nonneg_left ?_ hm
  refine Real.rpow_le_rpow_of_exponent_ge (Real.rpow_pos_of_pos ht _)
    (Real.rpow_le_one ht.le ht1 (by norm_num)) ?_
  have := min_le_right (1 / 8 : ℝ) (7 * κ / 2)
  linarith

end RegularityStructures.Phi43

end
