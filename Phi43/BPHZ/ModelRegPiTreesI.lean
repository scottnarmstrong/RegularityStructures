/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ModelRegPiTreesCore
public import Phi43.BPHZ.ModelRegPiTreesHint
public import Phi43.BPHZ.ModelRegPiTreesMoments
public import Phi43.BPHZ.SemigroupTestTreesI3Psi
public import Phi43.BPHZ.SemigroupTestTreesI2Psi2
public import Phi43.BPHZ.SemigroupTestTreesI3Psi2
public import RegularityStructures.Abstract.Model

/-!
# `q`-th moments of `Q_t Π_x τ (x)` for the `I`-trees

The same as `ModelRegPiTreesNoise` for `τ ∈ {I(Ψ³)Ψ, I(Ψ²)Ψ², I(Ψ³)Ψ²}`, under `κ̄ ≤ κ / 2`.
The second moments are those of `SemigroupTestTrees*`, with exponent `2 deg τ + κ` (`lam^(-7κ)`,
`lam^(-7κ)`, `lam^(-1 - 9κ)`), which give `t^((deg τ + κ̄)/4)` as soon as `κ̄ ≤ κ / 2`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures RegularityStructures.Phi43

/-- **`q`-th moment of the regularised `I(Ψ³)Ψ`-coordinate of the random models.**  Uniform in
`ε ∈ (0, 1]`, `t ∈ (0, 1]`, the base point `x`, the noise and the models. -/
theorem regPi_iPsiCubePsi_lintegral_enorm_pow_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (κ : Kappa) {κbar : ℝ} (hκbar : κbar ≤ κ.1 / 2) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}
      (Z : Ω → Model (phi43RegularityStructure κ) parabolicSemigroup),
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      (∀ᵐ ω ∂P, Statements.IsPhi43ModelOf N κ (ξ ω)
        ((hairerWickConstant N ρ ε, hairerSunsetConstant N ρ ε) : RenormalisationConstants)
        (Z ω)) →
      ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
        ∫⁻ ω, ‖(Z ω).regPi x (Pi.single Symbol.iPsiCubePsi 1) t x‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * t ^ (((phi43RegularityStructure κ).deg Symbol.iPsiCubePsi + κbar) /
            parabolicSemigroup.order)) ^ q := by
  obtain ⟨C₀, hC₀, h2⟩ := hairerI3PsiField_semigroupPeriodised_second_moment_le N hρ κ.2.1
  obtain ⟨A, hA, hAm⟩ := hairerI3PsiField_semigroupPeriodised_integrable_pow_le.{u} q hq
  refine ⟨max 1 (Real.sqrt A) * Real.sqrt C₀, by positivity, ?_⟩
  intro Ω _ P W ε ξ Z hW hε hξ hZ t ht x
  have := hW.isProbabilityMeasure
  obtain ⟨ht0, ht1⟩ := ht
  have hae := ae_regPi_single_iPsiCubePsi_eq hξ hZ ht0 x (hairerI3PsiField_kernel_integrable_ae N hρ hε.1 hW hξ ht0 x)
  obtain ⟨hint, hmom⟩ := hAm N hρ hW hε.1 hξ ht0 (spaceTimeProj x) x
  refine regPi_lintegral_enorm_pow_le_core (F := (fun ω => hairerI3PsiField N ρ ε ξ (spaceTimeProj x) ω)) (measurable_hairerI3PsiField_uncurry N hξ (spaceTimeProj x)) ht0 ht1 x hae hq hA hC₀
    (e := (2 * (-4 * κ.1) + κ.1)) ?_ hint hmom (h2 hW hε hξ ht0 ht1 x)
  have h : parabolicSemigroup.order = 4 := rfl
  rw [h, phi43RegularityStructure_deg]
  simp only [homogeneity]
  linarith [hκbar, κ.2.1]

/-- **`q`-th moment of the regularised `I(Ψ²)Ψ²`-coordinate of the random models.**  Uniform in
`ε ∈ (0, 1]`, `t ∈ (0, 1]`, the base point `x`, the noise and the models. -/
theorem regPi_iPsiSqPsiSq_lintegral_enorm_pow_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (κ : Kappa) {κbar : ℝ} (hκbar : κbar ≤ κ.1 / 2) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}
      (Z : Ω → Model (phi43RegularityStructure κ) parabolicSemigroup),
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      (∀ᵐ ω ∂P, Statements.IsPhi43ModelOf N κ (ξ ω)
        ((hairerWickConstant N ρ ε, hairerSunsetConstant N ρ ε) : RenormalisationConstants)
        (Z ω)) →
      ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
        ∫⁻ ω, ‖(Z ω).regPi x (Pi.single Symbol.iPsiSqPsiSq 1) t x‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * t ^ (((phi43RegularityStructure κ).deg Symbol.iPsiSqPsiSq + κbar) /
            parabolicSemigroup.order)) ^ q := by
  obtain ⟨C₀, hC₀, h2⟩ := hairerI2Psi2Field_semigroupPeriodised_second_moment_le N hρ κ.2.1
  obtain ⟨A, hA, hAm⟩ := hairerI2Psi2Field_semigroupPeriodised_integrable_pow_le.{u} q hq
  refine ⟨max 1 (Real.sqrt A) * Real.sqrt C₀, by positivity, ?_⟩
  intro Ω _ P W ε ξ Z hW hε hξ hZ t ht x
  have := hW.isProbabilityMeasure
  obtain ⟨ht0, ht1⟩ := ht
  have hae := ae_regPi_single_iPsiSqPsiSq_eq hξ hZ ht0 x (hairerI2Psi2Field_kernel_integrable_ae N hρ hε.1 hW hξ ht0 x)
  obtain ⟨hint, hmom⟩ := hAm N hρ hW hε.1 hξ ht0 (spaceTimeProj x) x
  refine regPi_lintegral_enorm_pow_le_core (F := (fun ω => hairerI2Psi2Field N ρ ε ξ (spaceTimeProj x) ω)) (measurable_hairerI2Psi2Field_uncurry N hξ (spaceTimeProj x)) ht0 ht1 x hae hq hA hC₀
    (e := (2 * (-4 * κ.1) + κ.1)) ?_ hint hmom (h2 hW hε hξ ht0 ht1 x)
  have h : parabolicSemigroup.order = 4 := rfl
  rw [h, phi43RegularityStructure_deg]
  simp only [homogeneity]
  linarith [hκbar, κ.2.1]

/-- **`q`-th moment of the regularised `I(Ψ³)Ψ²`-coordinate of the random models.**  Uniform in
`ε ∈ (0, 1]`, `t ∈ (0, 1]`, the base point `x`, the noise and the models. -/
theorem regPi_iPsiCubePsiSq_lintegral_enorm_pow_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (κ : Kappa) {κbar : ℝ} (hκbar : κbar ≤ κ.1 / 2) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}
      (Z : Ω → Model (phi43RegularityStructure κ) parabolicSemigroup),
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      (∀ᵐ ω ∂P, Statements.IsPhi43ModelOf N κ (ξ ω)
        ((hairerWickConstant N ρ ε, hairerSunsetConstant N ρ ε) : RenormalisationConstants)
        (Z ω)) →
      ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
        ∫⁻ ω, ‖(Z ω).regPi x (Pi.single Symbol.iPsiCubePsiSq 1) t x‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * t ^ (((phi43RegularityStructure κ).deg Symbol.iPsiCubePsiSq + κbar) /
            parabolicSemigroup.order)) ^ q := by
  obtain ⟨C₀, hC₀, h2⟩ := hairerI3Psi2Field_semigroupPeriodised_second_moment_le N hρ κ.2.1
  obtain ⟨A, hA, hAm⟩ := hairerI3Psi2Field_semigroupPeriodised_integrable_pow_le.{u} q hq
  refine ⟨max 1 (Real.sqrt A) * Real.sqrt C₀, by positivity, ?_⟩
  intro Ω _ P W ε ξ Z hW hε hξ hZ t ht x
  have := hW.isProbabilityMeasure
  obtain ⟨ht0, ht1⟩ := ht
  have hae := ae_regPi_single_iPsiCubePsiSq_eq hξ hZ ht0 x (hairerI3Psi2Field_kernel_integrable_ae N hρ hε.1 hW hξ ht0 x)
  obtain ⟨hint, hmom⟩ := hAm N hρ hW hε.1 hξ ht0 (spaceTimeProj x) x
  refine regPi_lintegral_enorm_pow_le_core (F := (fun ω => hairerI3Psi2Field N ρ ε ξ (spaceTimeProj x) ω)) (measurable_hairerI3Psi2Field_uncurry N hξ (spaceTimeProj x)) ht0 ht1 x hae hq hA hC₀
    (e := (-1 - 9 * κ.1)) ?_ hint hmom (h2 hW hε hξ ht0 ht1 x)
  have h : parabolicSemigroup.order = 4 := rfl
  rw [h, phi43RegularityStructure_deg]
  simp only [homogeneity]
  linarith [hκbar, κ.2.1]

end RegularityStructures.Phi43

end
