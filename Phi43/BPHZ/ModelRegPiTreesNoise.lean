/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ModelRegPiTreesCore
public import Phi43.BPHZ.ModelRegPiTreesHint
public import Phi43.BPHZ.ModelRegPiTreesMoments
public import Phi43.BPHZ.SemigroupTestTreesXi
public import Phi43.BPHZ.SemigroupTestWick
public import Phi43.BPHZ.SemigroupTestAllMoments
public import RegularityStructures.Abstract.Model

/-!
# `q`-th moments of `Q_t Π_x τ (x)` for `τ = Ξ, Ψ², Ψ³`

For the random models `Z ω` that are almost surely `IsPhi43ModelOf N κ (ξ ω) (c_ε, C₂) (Z ω)` with `ξ`
a regularised noise, and `τ ∈ {Ξ, Ψ², Ψ³}`, `t ∈ (0, 1]`, `ε ∈ (0, 1]`, `κ̄ ≤ κ`,

`∫⁻ ω, ‖(Z ω).regPi x (Pi.single τ 1) t x‖ₑ ^ q ≤ ofReal (C * t ^ ((deg τ + κ̄) / 4)) ^ q`

with `C` independent of `ε`, `t`, `x`, the noise and `Z` (the shape of `regPi_psi_lintegral_enorm_pow_le`).
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures RegularityStructures.Phi43

/-- **`q`-th moment of the regularised `Ξ`-coordinate of the random models.**  Uniform in
`ε ∈ (0, 1]`, `t ∈ (0, 1]`, the base point `x`, the noise and the models. -/
theorem regPi_noise_lintegral_enorm_pow_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (κ : Kappa) {κbar : ℝ} (hκbar : κbar ≤ κ.1) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}
      (Z : Ω → Model (phi43RegularityStructure κ) parabolicSemigroup),
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      (∀ᵐ ω ∂P, Statements.IsPhi43ModelOf N κ (ξ ω)
        ((hairerWickConstant N ρ ε, hairerSunsetConstant N ρ ε) : RenormalisationConstants)
        (Z ω)) →
      ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
        ∫⁻ ω, ‖(Z ω).regPi x (Pi.single Symbol.noise 1) t x‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * t ^ (((phi43RegularityStructure κ).deg Symbol.noise + κbar) /
            parabolicSemigroup.order)) ^ q := by
  obtain ⟨C₀, hC₀, h2⟩ := regularisedNoise_semigroupPeriodised_second_moment_le hρ
  obtain ⟨A, hA, hAm⟩ := regularisedNoise_semigroupPeriodised_integrable_pow_le.{u} q hq
  refine ⟨max 1 (Real.sqrt A) * Real.sqrt C₀, by positivity, ?_⟩
  intro Ω _ P W ε ξ Z hW hε hξ hZ t ht x
  have := hW.isProbabilityMeasure
  obtain ⟨ht0, ht1⟩ := ht
  have hae := ae_regPi_single_noise_eq hξ hZ ht0 x (regularisedNoise_kernel_integrable_ae hρ hε.1 hW hξ ht0 x)
  obtain ⟨hint, hmom⟩ := hAm hρ hW hε.1 hξ ht0 x
  refine regPi_lintegral_enorm_pow_le_core (F := (fun ω => ξ ω)) (regularisedNoise_measurable_uncurry P W ρ ε ξ hξ) ht0 ht1 x hae hq hA hC₀
    (e := (-(5 : ℝ))) ?_ hint hmom (h2 hW hε hξ ht0 ht1 x)
  have h : parabolicSemigroup.order = 4 := rfl
  rw [h, phi43RegularityStructure_deg]
  simp only [homogeneity]
  linarith [hκbar]

/-- **`q`-th moment of the regularised `Ψ²`-coordinate of the random models.**  Uniform in
`ε ∈ (0, 1]`, `t ∈ (0, 1]`, the base point `x`, the noise and the models. -/
theorem regPi_psiSq_lintegral_enorm_pow_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (κ : Kappa) {κbar : ℝ} (hκbar : κbar ≤ κ.1) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}
      (Z : Ω → Model (phi43RegularityStructure κ) parabolicSemigroup),
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      (∀ᵐ ω ∂P, Statements.IsPhi43ModelOf N κ (ξ ω)
        ((hairerWickConstant N ρ ε, hairerSunsetConstant N ρ ε) : RenormalisationConstants)
        (Z ω)) →
      ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
        ∫⁻ ω, ‖(Z ω).regPi x (Pi.single Symbol.psiSq 1) t x‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * t ^ (((phi43RegularityStructure κ).deg Symbol.psiSq + κbar) /
            parabolicSemigroup.order)) ^ q := by
  obtain ⟨C₀, hC₀, h2⟩ := hairerPsiWickSquare_semigroupPeriodised_second_moment_le N hρ
  obtain ⟨A, hA, hAm⟩ := hairerPsiWickSquare_semigroupPeriodised_integrable_pow_le.{u} q hq
  refine ⟨max 1 (Real.sqrt A) * Real.sqrt C₀, by positivity, ?_⟩
  intro Ω _ P W ε ξ Z hW hε hξ hZ t ht x
  have := hW.isProbabilityMeasure
  obtain ⟨ht0, ht1⟩ := ht
  have hae := ae_regPi_single_psiSq_eq hξ hZ ht0 x (hairerPsiWickSquare_kernel_integrable_ae N hρ hε.1 hW hξ ht0 x)
  obtain ⟨hint, hmom⟩ := hAm N hρ hW hε.1 hξ ht0 x
  refine regPi_lintegral_enorm_pow_le_core (F := (fun ω => hairerPsiWickSquare N ρ ε ξ ω)) (measurable_hairerPsiWickSquare_uncurry N hξ) ht0 ht1 x hae hq hA hC₀
    (e := (-(2 : ℝ))) ?_ hint hmom (h2 hW hε hξ ht0 ht1 x)
  have h : parabolicSemigroup.order = 4 := rfl
  rw [h, phi43RegularityStructure_deg]
  simp only [homogeneity]
  linarith [hκbar, κ.2.1]

/-- **`q`-th moment of the regularised `Ψ³`-coordinate of the random models.**  Uniform in
`ε ∈ (0, 1]`, `t ∈ (0, 1]`, the base point `x`, the noise and the models. -/
theorem regPi_psiCube_lintegral_enorm_pow_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (κ : Kappa) {κbar : ℝ} (hκbar : κbar ≤ κ.1) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}
      (Z : Ω → Model (phi43RegularityStructure κ) parabolicSemigroup),
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      (∀ᵐ ω ∂P, Statements.IsPhi43ModelOf N κ (ξ ω)
        ((hairerWickConstant N ρ ε, hairerSunsetConstant N ρ ε) : RenormalisationConstants)
        (Z ω)) →
      ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
        ∫⁻ ω, ‖(Z ω).regPi x (Pi.single Symbol.psiCube 1) t x‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * t ^ (((phi43RegularityStructure κ).deg Symbol.psiCube + κbar) /
            parabolicSemigroup.order)) ^ q := by
  obtain ⟨C₀, hC₀, h2⟩ := hairerPsiWickCube_semigroupPeriodised_second_moment_le N hρ
  obtain ⟨A, hA, hAm⟩ := hairerPsiWickCube_semigroupPeriodised_integrable_pow_le.{u} q hq
  refine ⟨max 1 (Real.sqrt A) * Real.sqrt C₀, by positivity, ?_⟩
  intro Ω _ P W ε ξ Z hW hε hξ hZ t ht x
  have := hW.isProbabilityMeasure
  obtain ⟨ht0, ht1⟩ := ht
  have hae := ae_regPi_single_psiCube_eq hξ hZ ht0 x (hairerPsiWickCube_kernel_integrable_ae N hρ hε.1 hW hξ ht0 x)
  obtain ⟨hint, hmom⟩ := hAm N hρ hW hε.1 hξ ht0 x
  refine regPi_lintegral_enorm_pow_le_core (F := (fun ω => hairerPsiWickCube N ρ ε ξ ω)) (measurable_hairerPsiWickCube_uncurry N hξ) ht0 ht1 x hae hq hA hC₀
    (e := (-(3 : ℝ))) ?_ hint hmom (h2 hW hε hξ ht0 ht1 x)
  have h : parabolicSemigroup.order = 4 := rfl
  rw [h, phi43RegularityStructure_deg]
  simp only [homogeneity]
  linarith [hκbar, κ.2.1]

end RegularityStructures.Phi43

end
