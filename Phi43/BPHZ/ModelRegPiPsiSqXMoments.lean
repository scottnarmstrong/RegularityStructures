/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ModelRegPiPsiSqXModel
public import Phi43.BPHZ.ModelRegPiPsiSqXSecond
public import Phi43.BPHZ.ModelRegPiPsiSqXMomentsAll
public import Phi43.BPHZ.ModelRegPiTestCore
public import Phi43.BPHZ.ModelRegPiTreesHint
public import RegularityStructures.Abstract.Model

/-!
# `q`-th moments of `Q_t Π_x (Ψ² Xᵢ) (x)` for the random models, and their differences

For the random models `Z ω` that are almost surely `IsPhi43ModelOf N κ (ξ ω) (c_ε, C₂) (Z ω)`,
`t ∈ (0, 1]`, `ε ∈ (0, 1]`, `κ̄ ≤ κ` and `i : Fin 3`,

`∫⁻ ω, ‖(Z ω).regPi x (Pi.single (Ψ²Xᵢ) 1) t x‖ₑ ^ q ≤ ofReal (C * t ^ ((deg (Ψ²Xᵢ) + κ̄) / 4)) ^ q`

(`regPi_psiSqX_lintegral_enorm_pow_le`), and for two models (`ρ, ε, ξ, Z`) and (`ρ', ε', ξ', Z'`)
of the same white noise, `0 ≤ κ̄`, `κ̄ + θ ≤ κ`, `θ > 0`,

`∫⁻ ω, ‖(Z ω).regPi x (Pi.single (Ψ²Xᵢ) 1) t x - (Z' ω).regPi x (Pi.single (Ψ²Xᵢ) 1) t x‖ₑ ^ q ≤
  ofReal (C * (max ε ε') ^ θ * t ^ ((deg (Ψ²Xᵢ) + κ̄) / 4)) ^ q`

(`regPi_psiSqX_sub_lintegral_enorm_pow_le`).  The realisation is the Wick square tested against the
coordinate-weighted periodised kernel `g_i` (`ae_regPi_single_psiSqX_eq`); `g_i = lam · (profile)`,
so the second moment is `lam² · lam⁻² = 1` (resp. `(max ε ε')^(2θ) lam^(-2θ)`), as `deg (Ψ²Xᵢ) = -2κ`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures RegularityStructures.Phi43

/-- **`q`-th moment of the regularised `Ψ² Xᵢ`-coordinate of the random models.**  Uniform in
`ε ∈ (0, 1]`, `t ∈ (0, 1]`, the base point `x`, the noise and the models. -/
theorem regPi_psiSqX_lintegral_enorm_pow_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (κ : Kappa) {κbar : ℝ} (hκbar : κbar ≤ κ.1) {q : ℕ} (hq : 1 ≤ q)
    (i : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}
      (Z : Ω → Model (phi43RegularityStructure κ) parabolicSemigroup),
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      (∀ᵐ ω ∂P, Statements.IsPhi43ModelOf N κ (ξ ω)
        ((hairerWickConstant N ρ ε, hairerSunsetConstant N ρ ε) : RenormalisationConstants)
        (Z ω)) →
      ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
        ∫⁻ ω, ‖(Z ω).regPi x (Pi.single (Symbol.psiSqX i) 1) t x‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * t ^ (((phi43RegularityStructure κ).deg (Symbol.psiSqX i) + κbar) /
            parabolicSemigroup.order)) ^ q := by
  obtain ⟨C₀, hC₀, h2⟩ := hairerPsiWickSquare_semigroupPeriodisedX_second_moment_le.{u} N hρ i
  obtain ⟨A, hA, hAm⟩ := hairerPsiWickSquare_semigroupPeriodisedX_integrable_pow_le.{u} q hq
  refine ⟨max 1 (Real.sqrt A) * Real.sqrt C₀, by positivity, ?_⟩
  intro Ω _ P W ε ξ Z hW hε hξ hZ t ht x
  have := hW.isProbabilityMeasure
  obtain ⟨ht0, ht1⟩ := ht
  have hint := kernel_coord_mul_field_integrable_ae_of_sq_bound
    (measurable_hairerPsiWickSquare_uncurry N hξ)
    (fun u => hairerPsiWickSquare_memLp N hρ hε.1 hW hξ u)
    (V := 2 * hairerCovariance N ρ ε 0 ^ 2) (fun u => by
      have h := hairerPsiWickSquare_integral_mul N hρ hε.1 hW hξ u u
      rw [sub_self] at h
      simpa only [sq] using h.le) ht0 x i
  have hae := ae_regPi_single_psiSqX_eq hξ hZ i ht0 x hint
  obtain ⟨hint', hmom⟩ := hAm N hρ hW hε.1 hξ ht0 x i
  refine regPi_lintegral_enorm_pow_le_core_of_test (g := semigroupPeriodisedX t x i)
    (measurable_semigroupPeriodisedX t x i)
    (F := fun ω => hairerPsiWickSquare N ρ ε ξ ω) (measurable_hairerPsiWickSquare_uncurry N hξ)
    ht0 ht1 hae hq hA hC₀ (e := (0 : ℝ)) ?_ hint' hmom
    (by rw [Real.rpow_zero, mul_one]; exact h2 hW hε hξ ht0 ht1 x)
  have h : parabolicSemigroup.order = 4 := rfl
  rw [h, phi43RegularityStructure_deg]
  simp only [homogeneity]
  have := κ.2.1
  linarith

/-- **Difference of the `q`-th moments of the regularised `Ψ² Xᵢ`-coordinate of two models.** -/
theorem regPi_psiSqX_sub_lintegral_enorm_pow_le (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') (κ : Kappa) {κbar θ : ℝ} (hκbar : 0 ≤ κbar)
    (hθ : 0 < θ) (hκθ : κbar + θ ≤ κ.1) {q : ℕ} (hq : 1 ≤ q) (i : Fin 3) :
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
        ∫⁻ ω, ‖(Z ω).regPi x (Pi.single (Symbol.psiSqX i) 1) t x -
            (Z' ω).regPi x (Pi.single (Symbol.psiSqX i) 1) t x‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * (max ε ε') ^ θ *
            t ^ (((phi43RegularityStructure κ).deg (Symbol.psiSqX i) + κbar) /
              parabolicSemigroup.order)) ^ q := by
  have hκ1 : κ.1 < 1 / 16 := κ.2.2
  have hκ0 : 0 < κ.1 := κ.2.1
  obtain ⟨C₀, hC₀, h2⟩ := hairerPsiWickSquare_sub_semigroupPeriodisedX_second_moment_le.{u} N hρ hρ'
    hθ (by linarith) i
  obtain ⟨A, hA, hAm⟩ := hairerPsiWickSquare_sub_semigroupPeriodisedX_integrable_pow_le.{u} q hq
  refine ⟨max 1 (Real.sqrt A) * Real.sqrt C₀, by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' Z Z' hW hε hε' hξ hξ' hZ hZ' t ht x
  have := hW.isProbabilityMeasure
  obtain ⟨ht0, ht1⟩ := ht
  have hint₁ := kernel_coord_mul_field_integrable_ae_of_sq_bound
    (measurable_hairerPsiWickSquare_uncurry N hξ)
    (fun u => hairerPsiWickSquare_memLp N hρ hε.1 hW hξ u)
    (V := 2 * hairerCovariance N ρ ε 0 ^ 2) (fun u => by
      have h := hairerPsiWickSquare_integral_mul N hρ hε.1 hW hξ u u
      rw [sub_self] at h
      simpa only [sq] using h.le) ht0 x i
  have hint₂ := kernel_coord_mul_field_integrable_ae_of_sq_bound
    (measurable_hairerPsiWickSquare_uncurry N hξ')
    (fun u => hairerPsiWickSquare_memLp N hρ' hε'.1 hW hξ' u)
    (V := 2 * hairerCovariance N ρ' ε' 0 ^ 2) (fun u => by
      have h := hairerPsiWickSquare_integral_mul N hρ' hε'.1 hW hξ' u u
      rw [sub_self] at h
      simpa only [sq] using h.le) ht0 x i
  have hae₁ := ae_regPi_single_psiSqX_eq hξ hZ i ht0 x hint₁
  have hae₂ := ae_regPi_single_psiSqX_eq hξ' hZ' i ht0 x hint₂
  obtain ⟨hint, hmom⟩ := hAm N hρ hρ' hW hε.1 hε'.1 hξ hξ' ht0 x i
  have hi₁ : ∀ᵐ ω ∂P, Integrable (fun u : SpaceTime =>
      semigroupPeriodisedX t x i u * hairerPsiWickSquare N ρ ε ξ ω u) := by
    filter_upwards [hint₁] with ω hω
    exact (integral_semigroup_kernel_coord_mul_comp_proj t x i
      (measurable_slice_of_uncurry (measurable_hairerPsiWickSquare_uncurry N hξ) ω) hω).1
  have hi₂ : ∀ᵐ ω ∂P, Integrable (fun u : SpaceTime =>
      semigroupPeriodisedX t x i u * hairerPsiWickSquare N ρ' ε' ξ' ω u) := by
    filter_upwards [hint₂] with ω hω
    exact (integral_semigroup_kernel_coord_mul_comp_proj t x i
      (measurable_slice_of_uncurry (measurable_hairerPsiWickSquare_uncurry N hξ') ω) hω).1
  refine regPi_sub_lintegral_enorm_pow_le_core_of_test (g := semigroupPeriodisedX t x i)
    (measurable_semigroupPeriodisedX t x i)
    (F₁ := fun ω => hairerPsiWickSquare N ρ ε ξ ω) (F₂ := fun ω => hairerPsiWickSquare N ρ' ε' ξ' ω)
    (measurable_hairerPsiWickSquare_uncurry N hξ) (measurable_hairerPsiWickSquare_uncurry N hξ')
    ht0 ht1 hae₁ hae₂ hi₁ hi₂ hq hA hC₀ (le_max_of_le_left hε.1.le) (e := (-(2 * θ))) ?_ hint hmom
    (h2 hW hε hε' hξ hξ' ht0 ht1 x)
  have h : parabolicSemigroup.order = 4 := rfl
  rw [h, phi43RegularityStructure_deg]
  simp only [homogeneity]
  linarith

end RegularityStructures.Phi43

end
