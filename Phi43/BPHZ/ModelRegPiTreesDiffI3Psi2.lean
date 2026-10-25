/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ModelRegPiTreesDiff
public import Phi43.BPHZ.ModelRegPiTreesI
public import Phi43.BPHZ.SemigroupTestTreesDiffI3Psi2Bound
public import Phi43.BPHZ.SemigroupTestTreesDiffMoments
public import RegularityStructures.Abstract.Model

/-!
# Difference of the `q`-th moments of `Q_t Π_x τ (x)` for `τ = I(Ψ³)Ψ²`

For two models `Z`, `Z'` that are almost surely `IsPhi43ModelOf` for the noises `ξ` (mollifier `ρ`,
scale `ε`) and `ξ'` (mollifier `ρ'`, scale `ε'`) of the same white noise, `κ̄ ≤ κ / 2`,
`0 < θ ≤ κ`, `t ∈ (0, 1]`, `ε, ε' ∈ (0, 1]`:

`∫⁻ ω, ‖(Z ω).regPi x (Pi.single τ 1) t x - (Z' ω).regPi x (Pi.single τ 1) t x‖ₑ ^ q ≤
  ofReal (C * (max ε ε') ^ θ * t ^ ((deg τ + κ̄) / 4)) ^ q`,

with `C` independent of `ε`, `ε'`, `t`, `x`, the noise and the models.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures RegularityStructures.Phi43

/-- **Difference of the `q`-th moments of the regularised `I(Ψ³)Ψ²`-coordinate of two models.** -/
theorem regPi_iPsiCubePsiSq_sub_lintegral_enorm_pow_le (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') (κ : Kappa) {κbar θ : ℝ}
    (hκbar : κbar ≤ κ.1 / 2) (hθ : 0 < θ) (hθκ : θ ≤ κ.1) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ}
      (Z Z' : Ω → Model (phi43RegularityStructure κ) parabolicSemigroup),
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      (∀ᵐ ω ∂P, Statements.IsPhi43ModelOf N κ (ξ ω)
        ((hairerWickConstant N ρ ε, hairerSunsetConstant N ρ ε) : RenormalisationConstants)
        (Z ω)) →
      (∀ᵐ ω ∂P, Statements.IsPhi43ModelOf N κ (ξ' ω)
        ((hairerWickConstant N ρ' ε', hairerSunsetConstant N ρ' ε') : RenormalisationConstants)
        (Z' ω)) →
      ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
        ∫⁻ ω, ‖(Z ω).regPi x (Pi.single Symbol.iPsiCubePsiSq 1) t x -
            (Z' ω).regPi x (Pi.single Symbol.iPsiCubePsiSq 1) t x‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * (max ε ε') ^ θ *
            t ^ (((phi43RegularityStructure κ).deg Symbol.iPsiCubePsiSq + κbar) /
              parabolicSemigroup.order)) ^ q := by
  have hκ1 : κ.1 < 1 / 16 := κ.2.2
  have hκ0 : 0 < κ.1 := κ.2.1
  obtain ⟨C₀, hC₀, h2⟩ := hairerI3Psi2Field_sub_semigroupPeriodised_second_moment_le N hρ hρ' hκ0
    hκ1.le hθ hθκ
  obtain ⟨A, hA, hAm⟩ := hairerI3Psi2Field_sub_semigroupPeriodised_integrable_pow_le.{u} q hq
  refine ⟨max 1 (Real.sqrt A) * Real.sqrt C₀, by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' Z Z' hW hε hε' hξ hξ' hZ hZ' t ht x
  have := hW.isProbabilityMeasure
  obtain ⟨ht0, ht1⟩ := ht
  have hint₁ := hairerI3Psi2Field_kernel_integrable_ae N hρ hε.1 hW hξ ht0 x
  have hint₂ := hairerI3Psi2Field_kernel_integrable_ae N hρ' hε'.1 hW hξ' ht0 x
  have hae₁ := ae_regPi_single_iPsiCubePsiSq_eq hξ hZ ht0 x hint₁
  have hae₂ := ae_regPi_single_iPsiCubePsiSq_eq hξ' hZ' ht0 x hint₂
  obtain ⟨hint, hmom⟩ := hAm N hρ hρ' hW hε.1 hε'.1 hξ hξ' ht0 (spaceTimeProj x) x
  refine regPi_sub_lintegral_enorm_pow_le_core
    (F₁ := fun ω => hairerI3Psi2Field N ρ ε ξ (spaceTimeProj x) ω)
    (F₂ := fun ω => hairerI3Psi2Field N ρ' ε' ξ' (spaceTimeProj x) ω)
    (measurable_hairerI3Psi2Field_uncurry N hξ (spaceTimeProj x))
    (measurable_hairerI3Psi2Field_uncurry N hξ' (spaceTimeProj x)) ht0 ht1 x hae₁ hae₂
    (ae_integrable_semigroupPeriodised_mul
      (measurable_hairerI3Psi2Field_uncurry N hξ (spaceTimeProj x)) t x hint₁)
    (ae_integrable_semigroupPeriodised_mul
      (measurable_hairerI3Psi2Field_uncurry N hξ' (spaceTimeProj x)) t x hint₂) hq hA hC₀
    (le_max_of_le_left hε.1.le) (e := -1 - 9 * κ.1) ?_ hint hmom
    (h2 hW hε hε' hξ hξ' ht0 ht1 x)
  have h : parabolicSemigroup.order = 4 := rfl
  rw [h, phi43RegularityStructure_deg]
  simp only [homogeneity]
  linarith [hκbar, κ.2.1]

end RegularityStructures.Phi43

end
