/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GammaMomentGradLp
import Mathlib.Tactic

/-!
# The `q`-th moments of `g_i` and `v₁` in Kolmogorov (`lintegral`) form

See `GammaMomentGradLp` for the statement of the results.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **The `q`-th moment of `g_i`.** -/
theorem gammaGrad_lintegral_enorm_pow_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ)
    (i : Fin 3) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ x y : SpaceTime, torusParabolicSize (y - x) ≤ 1 →
        ∫⁻ ω, ‖gammaGrad N ξ i x y ω‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * torusParabolicSize (y - x) ^ ((1 - δ) / 2)) ^ q := by
  obtain ⟨C₂, hC₂, h2⟩ := gammaGrad_second_moment_le.{u} N hρ i hδ hδ1
  obtain ⟨A, hA0, hA⟩ := gammaPsi_tested_integrable_pow_le.{u} q hq
  refine ⟨max 1 (Real.sqrt A) * Real.sqrt C₂, by positivity, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ x y hd
  have := hW.isProbabilityMeasure
  obtain ⟨hi, hm⟩ := hA N hρ hW hε.1 hξ (measurable_hairerGradIncrementKernel N i x y)
    (integrable_hairerGradIncrementKernel N i x y)
  have hmeas : Measurable fun ω => gammaGrad N ξ i x y ω := by
    have := measurable_integral_mul_field (measurable_hairerPsiField_uncurry N hξ)
      (measurable_hairerGradIncrementKernel N i x y)
    unfold gammaGrad
    simpa using this
  exact gammaMoment_lintegral_enorm_pow_le hmeas.aestronglyMeasurable hq hA0 hC₂
    (torusParabolicSize_nonneg _) (by ring) hi hm (h2 hW hε hξ x y hd)

/-- **The `q`-th moment of `v₁`.** -/
theorem gammaPsiTaylor_lintegral_enorm_pow_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ (x : SpaceTime) (t : ℝ) (a : Fin 3 → ℝ), parabolicNorm (t, a) ≤ 1 / 2 →
        ∫⁻ ω, ‖gammaPsiTaylor N ξ x t a ω‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * parabolicNorm (t, a) ^ ((3 - δ) / 2)) ^ q := by
  obtain ⟨C₂, hC₂, h2⟩ := gammaPsiTaylor_second_moment_le.{u} N hρ hδ hδ1
  obtain ⟨A, hA0, hA⟩ := gammaPsi_tested_integrable_pow_le.{u} q hq
  refine ⟨max 1 (Real.sqrt A) * Real.sqrt C₂, by positivity, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ x t a hn
  have := hW.isProbabilityMeasure
  obtain ⟨hi, hm⟩ := hA N hρ hW hε.1 hξ (measurable_hairerTaylorKernel N x t a)
    (integrable_hairerTaylorKernel N x t a)
  have hmeas : Measurable fun ω => gammaPsiTaylor N ξ x t a ω := by
    have := measurable_integral_mul_field (measurable_hairerPsiField_uncurry N hξ)
      (measurable_hairerTaylorKernel N x t a)
    unfold gammaPsiTaylor
    simpa using this
  exact gammaMoment_lintegral_enorm_pow_le hmeas.aestronglyMeasurable hq hA0 hC₂
    (parabolicNorm_nonneg _) (by ring) hi hm (h2 hW hε hξ x t a hn)

/-- **The `q`-th moment of `g_i` at the homogeneity `1/2 - κ`**, plus `κ̄ ∈ [0, κ/2]`. -/
theorem gammaGrad_lintegral_enorm_pow_le_kappa (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (i : Fin 3) {κ κ' : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1 / 4) (hκ'0 : 0 ≤ κ')
    (hκ' : κ' ≤ κ / 2) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ x y : SpaceTime, torusParabolicSize (y - x) ≤ 1 →
        ∫⁻ ω, ‖gammaGrad N ξ i x y ω‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * torusParabolicSize (y - x) ^ (1 / 2 - κ + κ')) ^ q := by
  obtain ⟨C, hC, h⟩ := gammaGrad_lintegral_enorm_pow_le N hρ i (δ := 2 * κ - 2 * κ')
    (by linarith) (by linarith) hq
  have e : (1 - (2 * κ - 2 * κ')) / 2 = 1 / 2 - κ + κ' := by ring
  rw [e] at h
  exact ⟨C, hC, h⟩

/-- **The `q`-th moment of `v₁` at the homogeneity `3/2 - κ`**, plus `κ̄ ∈ [0, κ/2]`. -/
theorem gammaPsiTaylor_lintegral_enorm_pow_le_kappa (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) {κ κ' : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1 / 4) (hκ'0 : 0 ≤ κ')
    (hκ' : κ' ≤ κ / 2) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ (x : SpaceTime) (t : ℝ) (a : Fin 3 → ℝ), parabolicNorm (t, a) ≤ 1 / 2 →
        ∫⁻ ω, ‖gammaPsiTaylor N ξ x t a ω‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * parabolicNorm (t, a) ^ (3 / 2 - κ + κ')) ^ q := by
  obtain ⟨C, hC, h⟩ := gammaPsiTaylor_lintegral_enorm_pow_le N hρ (δ := 2 * κ - 2 * κ')
    (by linarith) (by linarith) hq
  have e : (3 - (2 * κ - 2 * κ')) / 2 = 3 / 2 - κ + κ' := by ring
  rw [e] at h
  exact ⟨C, hC, h⟩

end RegularityStructures.Phi43

end
