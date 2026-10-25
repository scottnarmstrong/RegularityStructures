/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GammaMomentAll
public import Phi43.BPHZ.ModelRegPiMoment
import Mathlib.Tactic

/-!
# The `q`-th moments of `v₂` and `v₃` in Kolmogorov (`lintegral`) form

Combining the second-moment bounds `gammaWickSq_second_moment_le`, `gammaWickCube_second_moment_le` with
the moment equivalence `gammaWickSq_integrable_pow_le`, `gammaWickCube_integrable_pow_le` and
`lintegral_enorm_pow_le_of_moments`, for every `q ≥ 1`, `d = s(y - x) ≤ 1` and `ε ∈ (0, 1]`:

* `gammaWickSq_lintegral_enorm_pow_le`: `∫⁻ ‖v₂‖ₑ^q ≤ ofReal (C d^((2-δ)/2))^q`, `δ ∈ (0, 1]`;
* `gammaWickCube_lintegral_enorm_pow_le`: `∫⁻ ‖v₃‖ₑ^q ≤ ofReal (C d^((1-δ)/2))^q`, `δ ∈ (0, 1]`;

and the same with the exponents `1 - 2κ + κ̄` (degree of `I(Ψ²)`, plus `κ̄`) and `1/2 - 3κ + κ̄`
(degree of `I(Ψ³)`, plus `κ̄`) for `0 ≤ κ̄ ≤ κ/2` (`gammaWickSq_lintegral_enorm_pow_le_kappa`,
`gammaWickCube_lintegral_enorm_pow_le_kappa`).  The constants do not depend on `ε`, `x`, `y`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Measurability of a kernel integral of a jointly measurable random field. -/
theorem measurable_integral_mul_field {Y : Ω → SpaceTime → ℝ}
    (hY : Measurable fun q : Ω × SpaceTime => Y q.1 q.2) {g : SpaceTime → ℝ} (hg : Measurable g) :
    Measurable fun ω => ∫ w, g w * Y ω w :=
  (((hg.comp measurable_snd).mul hY).stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure SpaceTime))).measurable

/-- The arithmetic of the `q`-th moment from a second moment bound. -/
theorem gammaMoment_lintegral_enorm_pow_le {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → ℝ} (hY : AEStronglyMeasurable Y P) {q : ℕ} (hq : 1 ≤ q) {A C₂ r a t : ℝ}
    (hA : 0 ≤ A) (hC₂ : 0 ≤ C₂) (hr : 0 ≤ r) (ht : t = 2 * a)
    (hint : Integrable (fun ω => Y ω ^ (2 * q)) P)
    (hmom : ∫ ω, Y ω ^ (2 * q) ∂P ≤ A * (∫ ω, Y ω ^ 2 ∂P) ^ q)
    (h2 : ∫ ω, Y ω ^ 2 ∂P ≤ C₂ * r ^ t) :
    ∫⁻ ω, ‖Y ω‖ₑ ^ q ∂P ≤
      ENNReal.ofReal (max 1 (Real.sqrt A) * Real.sqrt C₂ * r ^ a) ^ q := by
  have hr2 : (r ^ a) ^ 2 = r ^ t := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hr]
    congr 1
    push_cast
    ring
  have hD : (Real.sqrt C₂ * r ^ a) ^ 2 = C₂ * r ^ t := by
    rw [mul_pow, Real.sq_sqrt hC₂, hr2]
  have h := Phi43.lintegral_enorm_pow_le_of_moments hY hq hA
    (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hr _)) hint hmom (hD ▸ h2)
  rwa [← mul_assoc] at h

/-- **The `q`-th moment of `v₂`.** -/
theorem gammaWickSq_lintegral_enorm_pow_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ x y : SpaceTime, torusParabolicSize (y - x) ≤ 1 →
        ∫⁻ ω, ‖gammaWickSq N ρ ε ξ x y ω‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * torusParabolicSize (y - x) ^ ((2 - δ) / 2)) ^ q := by
  obtain ⟨C₂, hC₂, h2⟩ := gammaWickSq_second_moment_le N hρ hδ hδ1
  obtain ⟨A, hA0, hA⟩ := gammaWickSq_integrable_pow_le q hq
  refine ⟨max 1 (Real.sqrt A) * Real.sqrt C₂, by positivity, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ x y hd
  have := hW.isProbabilityMeasure
  obtain ⟨hi, hm⟩ := hA N hρ hW hε.1 hξ x y
  have hmeas : Measurable fun ω => gammaWickSq N ρ ε ξ x y ω :=
    measurable_integral_mul_field (measurable_hairerPsiWickSquare_uncurry N hξ)
      (measurable_hairerI2Psi2Kernel N x y)
  exact gammaMoment_lintegral_enorm_pow_le hmeas.aestronglyMeasurable hq hA0 hC₂
    (torusParabolicSize_nonneg _) (by ring) hi hm (h2 hW hε hξ x y hd)

/-- **The `q`-th moment of `v₃`.** -/
theorem gammaWickCube_lintegral_enorm_pow_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ x y : SpaceTime, torusParabolicSize (y - x) ≤ 1 →
        ∫⁻ ω, ‖gammaWickCube N ρ ε ξ x y ω‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * torusParabolicSize (y - x) ^ ((1 - δ) / 2)) ^ q := by
  obtain ⟨C₂, hC₂, h2⟩ := gammaWickCube_second_moment_le N hρ hδ hδ1
  obtain ⟨A, hA0, hA⟩ := gammaWickCube_integrable_pow_le q hq
  refine ⟨max 1 (Real.sqrt A) * Real.sqrt C₂, by positivity, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ x y hd
  have := hW.isProbabilityMeasure
  obtain ⟨hi, hm⟩ := hA N hρ hW hε.1 hξ x y
  have hmeas : Measurable fun ω => gammaWickCube N ρ ε ξ x y ω :=
    measurable_integral_mul_field (measurable_hairerPsiWickCube_uncurry N hξ)
      (measurable_hairerI2Psi2Kernel N x y)
  exact gammaMoment_lintegral_enorm_pow_le hmeas.aestronglyMeasurable hq hA0 hC₂
    (torusParabolicSize_nonneg _) (by ring) hi hm (h2 hW hε hξ x y hd)

/-- **The `q`-th moment of `v₂` at the homogeneity of `I(Ψ²)`**: for `0 < κ ≤ 1/4` and
`0 ≤ κ̄ ≤ κ/2`, `∫⁻ ‖v₂‖ₑ^q ≤ ofReal (C d^(1 - 2κ + κ̄))^q`. -/
theorem gammaWickSq_lintegral_enorm_pow_le_kappa (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) {κ κ' : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1 / 4) (hκ'0 : 0 ≤ κ')
    (hκ' : κ' ≤ κ / 2) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ x y : SpaceTime, torusParabolicSize (y - x) ≤ 1 →
        ∫⁻ ω, ‖gammaWickSq N ρ ε ξ x y ω‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * torusParabolicSize (y - x) ^ (1 - 2 * κ + κ')) ^ q := by
  obtain ⟨C, hC, h⟩ := gammaWickSq_lintegral_enorm_pow_le N hρ (δ := 4 * κ - 2 * κ')
    (by linarith) (by linarith) hq
  have e : (2 - (4 * κ - 2 * κ')) / 2 = 1 - 2 * κ + κ' := by ring
  rw [e] at h
  exact ⟨C, hC, h⟩

/-- **The `q`-th moment of `v₃` at the homogeneity of `I(Ψ³)`**: for `0 < κ ≤ 1/6` and
`0 ≤ κ̄ ≤ κ/2`, `∫⁻ ‖v₃‖ₑ^q ≤ ofReal (C d^(1/2 - 3κ + κ̄))^q`. -/
theorem gammaWickCube_lintegral_enorm_pow_le_kappa (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) {κ κ' : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1 / 6) (hκ'0 : 0 ≤ κ')
    (hκ' : κ' ≤ κ / 2) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ x y : SpaceTime, torusParabolicSize (y - x) ≤ 1 →
        ∫⁻ ω, ‖gammaWickCube N ρ ε ξ x y ω‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * torusParabolicSize (y - x) ^ (1 / 2 - 3 * κ + κ')) ^ q := by
  obtain ⟨C, hC, h⟩ := gammaWickCube_lintegral_enorm_pow_le N hρ (δ := 6 * κ - 2 * κ')
    (by linarith) (by linarith) hq
  have e : (1 - (6 * κ - 2 * κ')) / 2 = 1 / 2 - 3 * κ + κ' := by ring
  rw [e] at h
  exact ⟨C, hC, h⟩

end RegularityStructures.Phi43

end
