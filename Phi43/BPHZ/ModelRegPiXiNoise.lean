/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ModelRegPiXiDiff
public import Phi43.BPHZ.ModelRegPiXiDiffMoments
public import Phi43.BPHZ.ModelRegPiTreesDiff
public import Phi43.BPHZ.ModelRegPiTreesHint
public import RegularityStructures.Abstract.Model

/-!
# Difference of the `q`-th moments of `Q_t Π_x Ξ (x)` for two models

For two models `Z`, `Z'` that are almost surely `IsPhi43ModelOf` for the noises `ξ` (mollifier `ρ`,
scale `ε`) and `ξ'` (mollifier `ρ'`, scale `ε'`) of the same white noise, `0 ≤ κ̄`, `κ̄ + θ ≤ κ`,
`θ > 0`, `t ∈ (0, 1]`, `ε, ε' ∈ (0, 1]`:

`∫⁻ ω, ‖(Z ω).regPi x (Pi.single Ξ 1) t x - (Z' ω).regPi x (Pi.single Ξ 1) t x‖ₑ ^ q ≤
  ofReal (C * (max ε ε') ^ θ * t ^ ((deg Ξ + κ̄) / 4)) ^ q`

(`regPi_noise_sub_lintegral_enorm_pow_le`), with `C` independent of `ε`, `ε'`, `t`, `x`, the
noise and the models.  The proof combines the `ε`-Hölder second moment bound
(`regularisedNoise_sub_semigroupPeriodised_second_moment_le`, exponent `2θ ≤ 1`) with the moment
equivalence of the first chaos.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures RegularityStructures.Phi43

/-- **Difference of the `q`-th moments of the regularised `Ξ`-coordinate of two models.** -/
theorem regPi_noise_sub_lintegral_enorm_pow_le (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') (κ : Kappa) {κbar θ : ℝ} (hκbar : 0 ≤ κbar)
    (hθ : 0 < θ) (hκθ : κbar + θ ≤ κ.1) {q : ℕ} (hq : 1 ≤ q) :
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
        ∫⁻ ω, ‖(Z ω).regPi x (Pi.single Symbol.noise 1) t x -
            (Z' ω).regPi x (Pi.single Symbol.noise 1) t x‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * (max ε ε') ^ θ *
            t ^ (((phi43RegularityStructure κ).deg Symbol.noise + κbar) /
              parabolicSemigroup.order)) ^ q := by
  have hκ1 : κ.1 < 1 / 16 := κ.2.2
  have hκ0 : 0 < κ.1 := κ.2.1
  obtain ⟨C₀, hC₀, h2⟩ := regularisedNoise_sub_semigroupPeriodised_second_moment_le.{u} hρ hρ'
    hθ.le (by linarith)
  obtain ⟨A, hA, hAm⟩ := regularisedNoise_sub_semigroupPeriodised_integrable_pow_le.{u} q hq
  refine ⟨max 1 (Real.sqrt A) * Real.sqrt C₀, by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' Z Z' hW hε hε' hξ hξ' hZ hZ' t ht x
  have := hW.isProbabilityMeasure
  obtain ⟨ht0, ht1⟩ := ht
  have hint₁ := regularisedNoise_kernel_integrable_ae hρ hε.1 hW hξ ht0 x
  have hint₂ := regularisedNoise_kernel_integrable_ae hρ' hε'.1 hW hξ' ht0 x
  have hae₁ := ae_regPi_single_noise_eq hξ hZ ht0 x hint₁
  have hae₂ := ae_regPi_single_noise_eq hξ' hZ' ht0 x hint₂
  obtain ⟨hint, hmom⟩ := hAm hρ hρ' hW hε.1 hε'.1 hξ hξ' ht0 x
  have hm₁ := regularisedNoise_measurable_uncurry P W ρ ε ξ hξ
  have hm₂ := regularisedNoise_measurable_uncurry P W ρ' ε' ξ' hξ'
  refine regPi_sub_lintegral_enorm_pow_le_core (F₁ := fun ω => ξ ω) (F₂ := fun ω => ξ' ω)
    hm₁ hm₂ ht0 ht1 x hae₁ hae₂
    (ae_integrable_semigroupPeriodised_mul hm₁ t x hint₁)
    (ae_integrable_semigroupPeriodised_mul hm₂ t x hint₂) hq hA hC₀
    (le_max_of_le_left hε.1.le) (e := (-(5 + 2 * θ))) ?_ hint hmom
    (h2 hW hε hε' hξ hξ' ht0 ht1 x)
  have h : parabolicSemigroup.order = 4 := rfl
  rw [h, phi43RegularityStructure_deg]
  simp only [homogeneity]
  linarith

end RegularityStructures.Phi43

end
