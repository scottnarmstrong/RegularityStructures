/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GammaFullPsiMoment
public import Phi43.BPHZ.GammaMomentGradBridgeIncrements
import Mathlib.Tactic

/-!
# Uniform moments of `K * Ψ` and `∇K * Ψ` at a point

With `T₀(z) = ∫ K♯(z - w) Ψ(w) dw` and `Tᵢ(z) = ∫ Gᵢ(z - w) Ψ(w) dw` (`K♯ = hairerKernelTorus N`,
`Gᵢ = hairerKernelTorusGrad N i`), for every `q ≥ 1` the moments `∫⁻ ‖T‖ₑ^q ≤ ofReal C ^ q` are
bounded uniformly in `z`, `ε ∈ (0, 1]`, the probability space (and `i`), and
`∫⁻ ‖T^ε - T^ε'‖ₑ^q ≤ ofReal (C (ε ∨ ε')^θ)^q` for `0 < θ ≤ 1/4`.  The kernel `K♯` has the
singularity `s⁻³` and `Gᵢ` has `s⁻⁴`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **Uniform `q`-th moment of `K ∗ Ψ` at a point.** -/
theorem gammaFull_conv_lintegral_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ)
    {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ z : SpaceTime, ∫⁻ ω, ‖∫ w, hairerKernelTorus N (z - w) * hairerPsiField N ξ ω w‖ₑ ^ q ∂P ≤
        ENNReal.ofReal C ^ q := by
  obtain ⟨C₁, hC₁, h⟩ := gammaFull_psiTest_lintegral_le.{u} N hρ (a := 3) (p := 9 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hq
  obtain ⟨B, hB, hK⟩ := i2Psi2KernelHyp_hairerKernelTorus N
  obtain ⟨-, hKm, hKs, hKb, -⟩ := hK
  exact ⟨C₁ * B, mul_nonneg hC₁ hB, fun hW hε hξ z =>
    h hW hε hξ hB hKm hKs hKb (integrable_hairerKernelTorus_sub N) z⟩

/-- **Uniform `q`-th moment of `∂ᵢ(K ∗ Ψ)` at a point.** -/
theorem gammaFull_grad_lintegral_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ)
    {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ (i : Fin 3) (z : SpaceTime),
        ∫⁻ ω, ‖∫ w, hairerKernelTorusGrad N i (z - w) * hairerPsiField N ξ ω w‖ₑ ^ q ∂P ≤
          ENNReal.ofReal C ^ q := by
  obtain ⟨C₁, hC₁, h⟩ := gammaFull_psiTest_lintegral_le.{u} N hρ (a := 4) (p := 3 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hq
  obtain ⟨B, hB, hK⟩ := hairerKernelTorusGrad_abs_le N
  exact ⟨C₁ * B, mul_nonneg hC₁ hB, fun hW hε hξ i z =>
    h hW hε hξ hB (measurable_hairerKernelTorusGrad N i)
      (fun u hu => hairerKernelTorusGrad_eq_zero_of_one_lt_time N i hu) (fun u hu => hK i hu)
      (fun z => integrable_comp_sub_left_spaceTime (integrable_hairerKernelTorusGrad N i) z) z⟩

/-- **Uniform `q`-th moment of `K ∗ (Ψ^ε - Ψ^ε')` at a point.** -/
theorem gammaFull_conv_sub_lintegral_le (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 4)
    {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' → ∀ z : SpaceTime,
      ∫⁻ ω, ‖(∫ w, hairerKernelTorus N (z - w) * hairerPsiField N ξ ω w) -
          ∫ w, hairerKernelTorus N (z - w) * hairerPsiField N ξ' ω w‖ₑ ^ q ∂P ≤
        ENNReal.ofReal (C * (max ε ε') ^ θ) ^ q := by
  obtain ⟨C₁, hC₁, h⟩ := gammaFull_psiTest_sub_lintegral_le.{u} N hρ hρ' (a := 3) (p := 9 / 4)
    hθ (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by linarith) hq
  obtain ⟨B, hB, hK⟩ := i2Psi2KernelHyp_hairerKernelTorus N
  obtain ⟨-, hKm, hKs, hKb, -⟩ := hK
  exact ⟨C₁ * B, mul_nonneg hC₁ hB, fun hW hε hε' hξ hξ' z => by
    simpa only [mul_assoc] using
      h hW hε hε' hξ hξ' hB hKm hKs hKb (integrable_hairerKernelTorus_sub N) z⟩

/-- **Uniform `q`-th moment of `∂ᵢ(K ∗ (Ψ^ε - Ψ^ε'))` at a point.** -/
theorem gammaFull_grad_sub_lintegral_le (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 4)
    {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' → ∀ (i : Fin 3) (z : SpaceTime),
      ∫⁻ ω, ‖(∫ w, hairerKernelTorusGrad N i (z - w) * hairerPsiField N ξ ω w) -
          ∫ w, hairerKernelTorusGrad N i (z - w) * hairerPsiField N ξ' ω w‖ₑ ^ q ∂P ≤
        ENNReal.ofReal (C * (max ε ε') ^ θ) ^ q := by
  obtain ⟨C₁, hC₁, h⟩ := gammaFull_psiTest_sub_lintegral_le.{u} N hρ hρ' (a := 4) (p := 3 / 2)
    hθ (by linarith) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by linarith) hq
  obtain ⟨B, hB, hK⟩ := hairerKernelTorusGrad_abs_le N
  exact ⟨C₁ * B, mul_nonneg hC₁ hB, fun hW hε hε' hξ hξ' i z => by
    simpa only [mul_assoc] using
      h hW hε hε' hξ hξ' hB (measurable_hairerKernelTorusGrad N i)
        (fun u hu => hairerKernelTorusGrad_eq_zero_of_one_lt_time N i hu)
        (fun u hu => hK i hu)
        (fun z => integrable_comp_sub_left_spaceTime (integrable_hairerKernelTorusGrad N i) z) z⟩

end RegularityStructures.Phi43

end
