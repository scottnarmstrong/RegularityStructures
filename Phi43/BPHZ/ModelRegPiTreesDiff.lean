/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ModelRegPiTreesDiffCore
public import Phi43.BPHZ.ModelRegPiTreesDiffMoments
public import Phi43.BPHZ.ModelRegPiTreesHint
public import Phi43.BPHZ.SemigroupTestDiffPsi
public import Phi43.BPHZ.SemigroupTestDiffWick
public import RegularityStructures.Abstract.Model

/-!
# Difference of the `q`-th moments of `Q_t Π_x τ (x)` for `τ = Ψ, Ψ², Ψ³`

For two models `Z`, `Z'` that are almost surely `IsPhi43ModelOf` for the noises `ξ` (mollifier `ρ`,
scale `ε`) and `ξ'` (mollifier `ρ'`, scale `ε'`) of the same white noise, `0 ≤ κ̄`, `κ̄ + θ ≤ κ`,
`θ > 0`, `t ∈ (0, 1]`, `ε, ε' ∈ (0, 1]`:

`∫⁻ ω, ‖(Z ω).regPi x (Pi.single τ 1) t x - (Z' ω).regPi x (Pi.single τ 1) t x‖ₑ ^ q ≤
  ofReal (C * (max ε ε') ^ θ * t ^ ((deg τ + κ̄) / 4)) ^ q`,

with `C` independent of `ε`, `ε'`, `t`, `x`, the noise and the models.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures RegularityStructures.Phi43

/-- Almost sure integrability of the kernel times a field on `ℝ⁴` gives integrability of the
periodised kernel times the field on `ℝ × T³`. -/
theorem ae_integrable_semigroupPeriodised_mul {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {F : Ω → SpaceTime → ℝ} (hF : Measurable fun q : Ω × SpaceTime => F q.1 q.2) (t : ℝ)
    (x : ParabolicSpace)
    (h : ∀ᵐ ω ∂P, Integrable (fun y : ParabolicSpace =>
      parabolicSemigroup.kernel t x y * F ω (spaceTimeProj y))) :
    ∀ᵐ ω ∂P, Integrable (fun u : SpaceTime => semigroupPeriodised t x u * F ω u) := by
  filter_upwards [h] with ω hω
  exact (integral_semigroup_kernel_mul_comp_proj t x (measurable_slice_of_uncurry hF ω) hω).1

/-- **Difference of the `q`-th moments of the regularised `Ψ`-coordinate of two models.** -/
theorem regPi_psi_sub_lintegral_enorm_pow_le (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
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
        ∫⁻ ω, ‖(Z ω).regPi x (Pi.single Symbol.psi 1) t x -
            (Z' ω).regPi x (Pi.single Symbol.psi 1) t x‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * (max ε ε') ^ θ *
            t ^ (((phi43RegularityStructure κ).deg Symbol.psi + κbar) /
              parabolicSemigroup.order)) ^ q := by
  have hκ1 : κ.1 < 1 / 16 := κ.2.2
  have hκ0 : 0 < κ.1 := κ.2.1
  obtain ⟨C₀, hC₀, h2⟩ := hairerPsiField_sub_semigroupPeriodised_second_moment_le N hρ hρ' hθ (by linarith)
  obtain ⟨A, hA, hAm⟩ := hairerPsiField_sub_semigroupPeriodised_integrable_pow_le.{u} q hq
  refine ⟨max 1 (Real.sqrt A) * Real.sqrt C₀, by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' Z Z' hW hε hε' hξ hξ' hZ hZ' t ht x
  have := hW.isProbabilityMeasure
  obtain ⟨ht0, ht1⟩ := ht
  have hint₁ := hairerPsiField_kernel_integrable_ae N hρ hε.1 hW hξ ht0 x
  have hint₂ := hairerPsiField_kernel_integrable_ae N hρ' hε'.1 hW hξ' ht0 x
  have hae₁ := ae_regPi_single_psi_eq hξ hZ ht0 x hint₁
  have hae₂ := ae_regPi_single_psi_eq hξ' hZ' ht0 x hint₂
  obtain ⟨hint, hmom⟩ := hAm N hρ hρ' hW hε.1 hε'.1 hξ hξ' ht0 x
  refine regPi_sub_lintegral_enorm_pow_le_core (F₁ := fun ω => hairerPsiField N ξ ω) (F₂ := fun ω => hairerPsiField N ξ' ω)
    (measurable_hairerPsiField_uncurry N hξ) (measurable_hairerPsiField_uncurry N hξ') ht0 ht1 x hae₁ hae₂
    (ae_integrable_semigroupPeriodised_mul (measurable_hairerPsiField_uncurry N hξ) t x hint₁)
    (ae_integrable_semigroupPeriodised_mul (measurable_hairerPsiField_uncurry N hξ') t x hint₂) hq hA hC₀
    (le_max_of_le_left hε.1.le) (e := (-(1 + 2 * θ))) ?_ hint hmom (h2 hW hε hε' hξ hξ' ht0 ht1 x)
  have h : parabolicSemigroup.order = 4 := rfl
  rw [h, phi43RegularityStructure_deg]
  simp only [homogeneity]
  linarith

/-- **Difference of the `q`-th moments of the regularised `Ψ²`-coordinate of two models.** -/
theorem regPi_psiSq_sub_lintegral_enorm_pow_le (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
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
        ∫⁻ ω, ‖(Z ω).regPi x (Pi.single Symbol.psiSq 1) t x -
            (Z' ω).regPi x (Pi.single Symbol.psiSq 1) t x‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * (max ε ε') ^ θ *
            t ^ (((phi43RegularityStructure κ).deg Symbol.psiSq + κbar) /
              parabolicSemigroup.order)) ^ q := by
  have hκ1 : κ.1 < 1 / 16 := κ.2.2
  have hκ0 : 0 < κ.1 := κ.2.1
  obtain ⟨C₀, hC₀, h2⟩ := hairerPsiWickSquare_sub_semigroupPeriodised_second_moment_le N hρ hρ' hθ (by linarith)
  obtain ⟨A, hA, hAm⟩ := hairerPsiWickSquare_sub_semigroupPeriodised_integrable_pow_le.{u} q hq
  refine ⟨max 1 (Real.sqrt A) * Real.sqrt C₀, by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' Z Z' hW hε hε' hξ hξ' hZ hZ' t ht x
  have := hW.isProbabilityMeasure
  obtain ⟨ht0, ht1⟩ := ht
  have hint₁ := hairerPsiWickSquare_kernel_integrable_ae N hρ hε.1 hW hξ ht0 x
  have hint₂ := hairerPsiWickSquare_kernel_integrable_ae N hρ' hε'.1 hW hξ' ht0 x
  have hae₁ := ae_regPi_single_psiSq_eq hξ hZ ht0 x hint₁
  have hae₂ := ae_regPi_single_psiSq_eq hξ' hZ' ht0 x hint₂
  obtain ⟨hint, hmom⟩ := hAm N hρ hρ' hW hε.1 hε'.1 hξ hξ' ht0 x
  refine regPi_sub_lintegral_enorm_pow_le_core (F₁ := fun ω => hairerPsiWickSquare N ρ ε ξ ω) (F₂ := fun ω => hairerPsiWickSquare N ρ' ε' ξ' ω)
    (measurable_hairerPsiWickSquare_uncurry N hξ) (measurable_hairerPsiWickSquare_uncurry N hξ') ht0 ht1 x hae₁ hae₂
    (ae_integrable_semigroupPeriodised_mul (measurable_hairerPsiWickSquare_uncurry N hξ) t x hint₁)
    (ae_integrable_semigroupPeriodised_mul (measurable_hairerPsiWickSquare_uncurry N hξ') t x hint₂) hq hA hC₀
    (le_max_of_le_left hε.1.le) (e := (-(2 + 2 * θ))) ?_ hint hmom (h2 hW hε hε' hξ hξ' ht0 ht1 x)
  have h : parabolicSemigroup.order = 4 := rfl
  rw [h, phi43RegularityStructure_deg]
  simp only [homogeneity]
  linarith

/-- **Difference of the `q`-th moments of the regularised `Ψ³`-coordinate of two models.** -/
theorem regPi_psiCube_sub_lintegral_enorm_pow_le (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
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
        ∫⁻ ω, ‖(Z ω).regPi x (Pi.single Symbol.psiCube 1) t x -
            (Z' ω).regPi x (Pi.single Symbol.psiCube 1) t x‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * (max ε ε') ^ θ *
            t ^ (((phi43RegularityStructure κ).deg Symbol.psiCube + κbar) /
              parabolicSemigroup.order)) ^ q := by
  have hκ1 : κ.1 < 1 / 16 := κ.2.2
  have hκ0 : 0 < κ.1 := κ.2.1
  obtain ⟨C₀, hC₀, h2⟩ := hairerPsiWickCube_sub_semigroupPeriodised_second_moment_le N hρ hρ' hθ (by linarith)
  obtain ⟨A, hA, hAm⟩ := hairerPsiWickCube_sub_semigroupPeriodised_integrable_pow_le.{u} q hq
  refine ⟨max 1 (Real.sqrt A) * Real.sqrt C₀, by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' Z Z' hW hε hε' hξ hξ' hZ hZ' t ht x
  have := hW.isProbabilityMeasure
  obtain ⟨ht0, ht1⟩ := ht
  have hint₁ := hairerPsiWickCube_kernel_integrable_ae N hρ hε.1 hW hξ ht0 x
  have hint₂ := hairerPsiWickCube_kernel_integrable_ae N hρ' hε'.1 hW hξ' ht0 x
  have hae₁ := ae_regPi_single_psiCube_eq hξ hZ ht0 x hint₁
  have hae₂ := ae_regPi_single_psiCube_eq hξ' hZ' ht0 x hint₂
  obtain ⟨hint, hmom⟩ := hAm N hρ hρ' hW hε.1 hε'.1 hξ hξ' ht0 x
  refine regPi_sub_lintegral_enorm_pow_le_core (F₁ := fun ω => hairerPsiWickCube N ρ ε ξ ω) (F₂ := fun ω => hairerPsiWickCube N ρ' ε' ξ' ω)
    (measurable_hairerPsiWickCube_uncurry N hξ) (measurable_hairerPsiWickCube_uncurry N hξ') ht0 ht1 x hae₁ hae₂
    (ae_integrable_semigroupPeriodised_mul (measurable_hairerPsiWickCube_uncurry N hξ) t x hint₁)
    (ae_integrable_semigroupPeriodised_mul (measurable_hairerPsiWickCube_uncurry N hξ') t x hint₂) hq hA hC₀
    (le_max_of_le_left hε.1.le) (e := (-(3 + 2 * θ))) ?_ hint hmom (h2 hW hε hε' hξ hξ' ht0 ht1 x)
  have h : parabolicSemigroup.order = 4 := rfl
  rw [h, phi43RegularityStructure_deg]
  simp only [homogeneity]
  linarith

end RegularityStructures.Phi43

end
