/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GammaFullPsiTest
import Mathlib.Tactic

/-!
# Uniform `q`-th moments of a single translated kernel test of `Ψ`

From the uniform second moments of `GammaFullPsiTest` and the moment equivalence for the tested
Gaussian field, for `q ≥ 1`, a kernel `K` as there, and every `z`:

* `∫⁻ ‖∫ K(z - w) Ψ(w) dw‖ₑ^q ≤ ofReal (C B)^q` (`gammaFull_psiTest_lintegral_le`);
* `∫⁻ ‖∫ K(z - w) (Ψ^ε - Ψ^ε')(w) dw‖ₑ^q ≤ ofReal (C B (ε ∨ ε')^θ)^q`
  (`gammaFull_psiTest_sub_lintegral_le`).
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- A kernel `K(z - ·)` supported in `|t| ≤ 1` with `|K| ≤ B s⁻ᵃ` has the trivial majorant at
`x = y = z`. -/
theorem gammaFull_gammaMajorant_shift {K : SpaceTime → ℝ} {B a : ℝ} (hB : 0 ≤ B)
    (hKm : Measurable K) (hKs : ∀ u : SpaceTime, 1 < |u.1| → K u = 0)
    (hKb : ∀ u : SpaceTime, 0 < torusParabolicSize u → |K u| ≤ B * torusParabolicSize u ^ (-a))
    (z : SpaceTime) : gammaMajorant (fun w => K (z - w)) z z 1 B 0 a := by
  refine ⟨zero_le_one, hB, hKm.comp (measurable_const.sub measurable_id), ?_⟩
  intro w hy _
  by_cases hs : |w.1 - z.1| ≤ 2
  · rw [i2Psi2Slab_of_le hs, one_mul]
    have h := hKb (z - w) hy
    have hn : 0 ≤ torusParabolicSize (z - w) ^ (-a) := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
    simp only [Real.one_rpow, mul_one]
    generalize torusParabolicSize (z - w) ^ (-a) = S at h hn ⊢
    nlinarith [mul_nonneg hB hn]
  · have h0 : K (z - w) = 0 := by
      refine hKs _ ?_
      simp only [Prod.fst_sub]
      rw [abs_sub_comm]
      linarith [not_le.1 hs]
    have : i2Psi2Slab z.1 w = 0 := by unfold i2Psi2Slab; simp [hs]
    show |K (z - w)| ≤ _
    rw [h0, this]
    simp

/-- **Uniform `q`-th moment of a single kernel test of `Ψ`.** -/
theorem gammaFull_psiTest_lintegral_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ)
    {a p : ℝ} (ha : 0 < a) (ha5 : a < 5) (hp5 : p < 5) (hap : 5 < a + p)
    (h2a : 2 * a + p < 10) (hp1 : 1 ≤ p) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ {K : SpaceTime → ℝ} {B : ℝ}, 0 ≤ B → Measurable K →
      (∀ u : SpaceTime, 1 < |u.1| → K u = 0) →
      (∀ u : SpaceTime, 0 < torusParabolicSize u → |K u| ≤ B * torusParabolicSize u ^ (-a)) →
      (∀ z : SpaceTime, Integrable fun w => K (z - w)) → ∀ z : SpaceTime,
      ∫⁻ ω, ‖∫ w, K (z - w) * hairerPsiField N ξ ω w‖ₑ ^ q ∂P ≤
        ENNReal.ofReal (C * B) ^ q := by
  obtain ⟨C₂, hC₂, h2⟩ := gammaFull_psiTest_second_le.{u} N hρ ha ha5 hp5 hap h2a hp1
  obtain ⟨A, hA0, hA⟩ := gammaPsi_tested_integrable_pow_le.{u} q hq
  refine ⟨max 1 (Real.sqrt A) * Real.sqrt C₂, by positivity, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ K B hB hKm hKs hKb hKi z
  have := hW.isProbabilityMeasure
  have hf : Measurable fun w : SpaceTime => K (z - w) :=
    hKm.comp (measurable_const.sub measurable_id)
  obtain ⟨hi, hm⟩ := hA N hρ hW hε.1 hξ hf (hKi z)
  have hmeas : Measurable fun ω => ∫ w, K (z - w) * hairerPsiField N ξ ω w :=
    measurable_integral_mul_field (measurable_hairerPsiField_uncurry N hξ) hf
  have h := gammaMoment_lintegral_enorm_pow_le hmeas.aestronglyMeasurable hq hA0
    (mul_nonneg hC₂ (sq_nonneg B)) zero_le_one (r := 1) (a := 0) (t := 0) (by ring) hi hm
    (by simpa using h2 hW hε hξ hB hKm hKs hKb hKi z)
  have e : max 1 (Real.sqrt A) * Real.sqrt (C₂ * B ^ 2) * (1 : ℝ) ^ (0 : ℝ) =
      max 1 (Real.sqrt A) * Real.sqrt C₂ * B := by
    rw [Real.sqrt_mul hC₂, Real.sqrt_sq hB]
    simp [mul_assoc]
  rw [e] at h
  exact h

/-- **Uniform `q`-th moment of a single kernel test of `Ψ^ε - Ψ^ε'`.** -/
theorem gammaFull_psiTest_sub_lintegral_le (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {θ a p : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (ha : 0 < a) (ha5 : a < 5) (hp5 : p < 5) (hap : 5 < a + p) (h2a : 2 * a + p < 10)
    (hp1 : 1 + 2 * θ ≤ p) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ {K : SpaceTime → ℝ} {B : ℝ}, 0 ≤ B → Measurable K →
      (∀ u : SpaceTime, 1 < |u.1| → K u = 0) →
      (∀ u : SpaceTime, 0 < torusParabolicSize u → |K u| ≤ B * torusParabolicSize u ^ (-a)) →
      (∀ z : SpaceTime, Integrable fun w => K (z - w)) → ∀ z : SpaceTime,
      ∫⁻ ω, ‖(∫ w, K (z - w) * hairerPsiField N ξ ω w) -
          ∫ w, K (z - w) * hairerPsiField N ξ' ω w‖ₑ ^ q ∂P ≤
        ENNReal.ofReal (C * B * (max ε ε') ^ θ) ^ q := by
  obtain ⟨C₂, hC₂, h2⟩ := gammaFull_psiTest_sub_second_le.{u} N hρ hρ' hθ hθ1 ha ha5 hp5 hap
    h2a hp1
  obtain ⟨A, hA0, hA⟩ := gammaPsi_tested_sub_integrable_pow_le.{u} q hq
  refine ⟨max 1 (Real.sqrt A) * Real.sqrt C₂, by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' K B hB hKm hKs hKb hKi z
  have := hW.isProbabilityMeasure
  have hf : Measurable fun w : SpaceTime => K (z - w) :=
    hKm.comp (measurable_const.sub measurable_id)
  obtain ⟨hi, hm⟩ := hA N hρ hρ' hW hε.1 hε'.1 hξ hξ'
    (gammaFull_gammaMajorant_shift hB hKm hKs hKb z) (hKi z) (by simp)
  have hmeas : Measurable fun ω => (∫ w, K (z - w) * hairerPsiField N ξ ω w) -
      ∫ w, K (z - w) * hairerPsiField N ξ' ω w :=
    (measurable_integral_mul_field (measurable_hairerPsiField_uncurry N hξ) hf).sub
      (measurable_integral_mul_field (measurable_hairerPsiField_uncurry N hξ') hf)
  have h := gammaMoment_lintegral_enorm_pow_le_sub hmeas.aestronglyMeasurable hq hA0
    (mul_nonneg hC₂ (sq_nonneg B)) (le_max_of_le_left hε.1.le) zero_le_one (r := 1) (a := 0)
    (t := 0) (θ := θ) (by ring) hi hm
    (by
      have := h2 hW hε hε' hξ hξ' hB hKm hKs hKb hKi z
      simpa [mul_assoc, mul_comm, mul_left_comm] using this)
  have e : max 1 (Real.sqrt A) * Real.sqrt (C₂ * B ^ 2) * (max ε ε') ^ θ * (1 : ℝ) ^ (0 : ℝ) =
      max 1 (Real.sqrt A) * Real.sqrt C₂ * B * (max ε ε') ^ θ := by
    rw [Real.sqrt_mul hC₂, Real.sqrt_sq hB]
    simp [mul_assoc]
  rw [e] at h
  exact h

end RegularityStructures.Phi43

end
