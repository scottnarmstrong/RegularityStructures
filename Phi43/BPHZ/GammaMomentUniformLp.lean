/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GammaMomentUniformSub
import Mathlib.Tactic

/-!
# Uniform `q`-th moments of `v₂`, `v₃` and of their two-scale differences

Combining the uniform second moments (`Phi43.BPHZ.GammaMomentUniform`,
`Phi43.BPHZ.GammaMomentUniformSub`) with the moment equivalence (`gammaWickSq_integrable_pow_le`,
`gammaWickSq_sub_integrable_pow_le`, ...), for every `q ≥ 1` and all `x, y` (no restriction on
`s(y - x)`):

* `∫⁻ ‖v_n(x, y)‖ₑ^q ≤ ofReal C ^ q`;
* `∫⁻ ‖v_n^ε(x, y) - v_n^ε'(x, y)‖ₑ^q ≤ ofReal (C (ε ∨ ε')^θ) ^ q`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **Uniform `q`-th moment of `v₂`.** -/
theorem gammaWickSq_lintegral_enorm_pow_le_uniform (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ x y : SpaceTime, ∫⁻ ω, ‖gammaWickSq N ρ ε ξ x y ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal C ^ q := by
  obtain ⟨C₂, hC₂, h2⟩ := gammaWickSq_second_moment_le_uniform N hρ
  obtain ⟨A, hA0, hA⟩ := gammaWickSq_integrable_pow_le.{u} q hq
  refine ⟨max 1 (Real.sqrt A) * Real.sqrt C₂, by positivity, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ x y
  have := hW.isProbabilityMeasure
  obtain ⟨hi, hm⟩ := hA N hρ hW hε.1 hξ x y
  have hmeas : Measurable fun ω => gammaWickSq N ρ ε ξ x y ω :=
    measurable_integral_mul_field (measurable_hairerPsiWickSquare_uncurry N hξ)
      (measurable_hairerI2Psi2Kernel N x y)
  have h := gammaMoment_lintegral_enorm_pow_le hmeas.aestronglyMeasurable hq hA0 hC₂
    (r := 1) (a := 0) (t := 0) zero_le_one (by ring) hi hm
    (by simpa using h2 hW hε hξ x y)
  simpa using h

/-- **Uniform `q`-th moment of `v₃`.** -/
theorem gammaWickCube_lintegral_enorm_pow_le_uniform (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ x y : SpaceTime, ∫⁻ ω, ‖gammaWickCube N ρ ε ξ x y ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal C ^ q := by
  obtain ⟨C₂, hC₂, h2⟩ := gammaWickCube_second_moment_le_uniform N hρ
  obtain ⟨A, hA0, hA⟩ := gammaWickCube_integrable_pow_le.{u} q hq
  refine ⟨max 1 (Real.sqrt A) * Real.sqrt C₂, by positivity, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ x y
  have := hW.isProbabilityMeasure
  obtain ⟨hi, hm⟩ := hA N hρ hW hε.1 hξ x y
  have hmeas : Measurable fun ω => gammaWickCube N ρ ε ξ x y ω :=
    measurable_integral_mul_field (measurable_hairerPsiWickCube_uncurry N hξ)
      (measurable_hairerI2Psi2Kernel N x y)
  have h := gammaMoment_lintegral_enorm_pow_le hmeas.aestronglyMeasurable hq hA0 hC₂
    (r := 1) (a := 0) (t := 0) zero_le_one (by ring) hi hm
    (by simpa using h2 hW hε hξ x y)
  simpa using h

/-- **Uniform `q`-th moment of `v₂^ε - v₂^ε'`.** -/
theorem gammaWickSq_sub_lintegral_enorm_pow_le_uniform (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 4)
    {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ x y : SpaceTime,
        ∫⁻ ω, ‖gammaWickSq N ρ ε ξ x y ω - gammaWickSq N ρ' ε' ξ' x y ω‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * (max ε ε') ^ θ) ^ q := by
  obtain ⟨C₂, hC₂, h2⟩ := gammaWickSq_sub_second_moment_le_uniform N hρ hρ' hθ hθ1
  obtain ⟨A, hA0, hA⟩ := gammaWickSq_sub_integrable_pow_le.{u} q hq
  refine ⟨max 1 (Real.sqrt A) * Real.sqrt C₂, by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' x y
  have := hW.isProbabilityMeasure
  obtain ⟨hi, hm⟩ := hA N hρ hρ' hW hε.1 hε'.1 hξ hξ' x y
  have hmeas : Measurable fun ω => gammaWickSq N ρ ε ξ x y ω - gammaWickSq N ρ' ε' ξ' x y ω :=
    (measurable_integral_mul_field (measurable_hairerPsiWickSquare_uncurry N hξ)
      (measurable_hairerI2Psi2Kernel N x y)).sub
    (measurable_integral_mul_field (measurable_hairerPsiWickSquare_uncurry N hξ')
      (measurable_hairerI2Psi2Kernel N x y))
  have h := gammaMoment_lintegral_enorm_pow_le_sub hmeas.aestronglyMeasurable hq hA0 hC₂
    (le_max_of_le_left hε.1.le) zero_le_one (a := 0) (t := 0) (r := 1) (by ring) hi hm
    (by simpa using h2 hW hε hε' hξ hξ' x y)
  simpa [mul_assoc] using h

/-- **Uniform `q`-th moment of `v₃^ε - v₃^ε'`.** -/
theorem gammaWickCube_sub_lintegral_enorm_pow_le_uniform (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 4)
    {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ x y : SpaceTime,
        ∫⁻ ω, ‖gammaWickCube N ρ ε ξ x y ω - gammaWickCube N ρ' ε' ξ' x y ω‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * (max ε ε') ^ θ) ^ q := by
  obtain ⟨C₂, hC₂, h2⟩ := gammaWickCube_sub_second_moment_le_uniform N hρ hρ' hθ hθ1
  obtain ⟨A, hA0, hA⟩ := gammaWickCube_sub_integrable_pow_le.{u} q hq
  refine ⟨max 1 (Real.sqrt A) * Real.sqrt C₂, by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' x y
  have := hW.isProbabilityMeasure
  obtain ⟨hi, hm⟩ := hA N hρ hρ' hW hε.1 hε'.1 hξ hξ' x y
  have hmeas : Measurable fun ω => gammaWickCube N ρ ε ξ x y ω - gammaWickCube N ρ' ε' ξ' x y ω :=
    (measurable_integral_mul_field (measurable_hairerPsiWickCube_uncurry N hξ)
      (measurable_hairerI2Psi2Kernel N x y)).sub
    (measurable_integral_mul_field (measurable_hairerPsiWickCube_uncurry N hξ')
      (measurable_hairerI2Psi2Kernel N x y))
  have h := gammaMoment_lintegral_enorm_pow_le_sub hmeas.aestronglyMeasurable hq hA0 hC₂
    (le_max_of_le_left hε.1.le) zero_le_one (a := 0) (t := 0) (r := 1) (by ring) hi hm
    (by simpa using h2 hW hε hε' hξ hξ' x y)
  simpa [mul_assoc] using h

end RegularityStructures.Phi43

end
