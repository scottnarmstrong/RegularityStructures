/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GammaMomentGradDiff
import Mathlib.Tactic

/-!
# The `q`-th moments of the two-scale differences of `g_i` and `v₁`

Kolmogorov (`lintegral`) forms; see `GammaMomentGradDiff` for the second-moment bounds.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **The `q`-th moment of `g_i^ε - g_i^ε'`.** -/
theorem gammaGrad_sub_lintegral_enorm_pow_le (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') (i : Fin 3) {θ δ : ℝ} (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (hδ : 0 < δ) (hθδ : 2 * θ + δ ≤ 1) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ x y : SpaceTime, torusParabolicSize (y - x) ≤ 1 →
        ∫⁻ ω, ‖gammaGrad N ξ i x y ω - gammaGrad N ξ' i x y ω‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * (max ε ε') ^ θ *
            torusParabolicSize (y - x) ^ ((1 - 2 * θ - δ) / 2)) ^ q := by
  obtain ⟨C₂, hC₂, h2⟩ := gammaGrad_sub_second_moment_le N hρ hρ' i hθ hθ1 hδ hθδ
  obtain ⟨A, hA0, hA⟩ := gammaPsi_tested_sub_integrable_pow_le.{u} q hq
  obtain ⟨M, hM, hMaj⟩ := gammaMajorant_hairerGradIncrement N i (γ := (1 - 2 * θ - δ) / 2)
    (by linarith) (by linarith)
  refine ⟨max 1 (Real.sqrt A) * Real.sqrt C₂, by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' x y hd
  have := hW.isProbabilityMeasure
  have hxy : |y.1 - x.1| ≤ 1 := gammaMoment_abs_time_le_one hd rfl
  obtain ⟨hi, hm⟩ := hA N hρ hρ' hW hε.1 hε'.1 hξ hξ' (hMaj hxy)
    (integrable_hairerGradIncrementKernel N i x y) hxy
  have m1 : Measurable fun ω => gammaGrad N ξ i x y ω := by
    have := measurable_integral_mul_field (measurable_hairerPsiField_uncurry N hξ)
      (measurable_hairerGradIncrementKernel N i x y)
    unfold gammaGrad
    simpa using this
  have m2 : Measurable fun ω => gammaGrad N ξ' i x y ω := by
    have := measurable_integral_mul_field (measurable_hairerPsiField_uncurry N hξ')
      (measurable_hairerGradIncrementKernel N i x y)
    unfold gammaGrad
    simpa using this
  have hmeas : Measurable fun ω => gammaGrad N ξ i x y ω - gammaGrad N ξ' i x y ω := m1.sub m2
  exact gammaMoment_lintegral_enorm_pow_le_sub hmeas.aestronglyMeasurable hq hA0 hC₂
    (le_max_of_le_left hε.1.le) (torusParabolicSize_nonneg _) (by ring) hi hm
    (h2 hW hε hε' hξ hξ' x y hd)

/-- **The `q`-th moment of `v₁^ε - v₁^ε'`.** -/
theorem gammaPsiTaylor_sub_lintegral_enorm_pow_le (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hδ : 0 < δ) (hθδ : 2 * θ + δ ≤ 1) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ (x : SpaceTime) (t : ℝ) (a : Fin 3 → ℝ), parabolicNorm (t, a) ≤ 1 / 2 →
        ∫⁻ ω, ‖gammaPsiTaylor N ξ x t a ω - gammaPsiTaylor N ξ' x t a ω‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * (max ε ε') ^ θ *
            parabolicNorm (t, a) ^ ((3 - 2 * θ - δ) / 2)) ^ q := by
  obtain ⟨C₂, hC₂, h2⟩ := gammaPsiTaylor_sub_second_moment_le N hρ hρ' hθ hθ1 hδ hθδ
  obtain ⟨A, hA0, hA⟩ := gammaPsi_tested_sub_integrable_pow_le.{u} q hq
  obtain ⟨M, hM, hMaj⟩ := gammaMajorant_hairerTaylorKernel N (θ := (1 - 2 * θ - δ) / 2)
    (by linarith) (by linarith)
  refine ⟨max 1 (Real.sqrt A) * Real.sqrt C₂, by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' x t a hn
  have := hW.isProbabilityMeasure
  have hai : ∀ i, |a i| ≤ 1 / 2 := fun i => by
    refine (Finset.single_le_sum (f := fun j => |a j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)).trans ?_
    simp only [parabolicNorm] at hn
    linarith [Real.sqrt_nonneg |t|]
  have ht : |t| ≤ 1 := by
    have h1 : √|t| ≤ 1 / 2 := by
      simp only [parabolicNorm] at hn
      linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => abs_nonneg (a i)]
    have h2 : |t| ≤ (1 / 2) ^ 2 := by
      rw [← Real.sqrt_le_left (by norm_num)]; exact h1
    linarith
  have hxy : |(x + (t, torusProj a)).1 - x.1| ≤ 1 := by simpa using ht
  obtain ⟨hi, hm⟩ := hA N hρ hρ' hW hε.1 hε'.1 hξ hξ' (hMaj hai ht)
    (integrable_hairerTaylorKernel N x t a) hxy
  have m1 : Measurable fun ω => gammaPsiTaylor N ξ x t a ω := by
    have := measurable_integral_mul_field (measurable_hairerPsiField_uncurry N hξ)
      (measurable_hairerTaylorKernel N x t a)
    unfold gammaPsiTaylor
    simpa using this
  have m2 : Measurable fun ω => gammaPsiTaylor N ξ' x t a ω := by
    have := measurable_integral_mul_field (measurable_hairerPsiField_uncurry N hξ')
      (measurable_hairerTaylorKernel N x t a)
    unfold gammaPsiTaylor
    simpa using this
  have hmeas : Measurable fun ω => gammaPsiTaylor N ξ x t a ω - gammaPsiTaylor N ξ' x t a ω := m1.sub m2
  exact gammaMoment_lintegral_enorm_pow_le_sub hmeas.aestronglyMeasurable hq hA0 hC₂
    (le_max_of_le_left hε.1.le) (parabolicNorm_nonneg _) (by ring) hi hm
    (h2 hW hε hε' hξ hξ' x t a hn)

/-- **The `q`-th moment of `g_i^ε - g_i^ε'` at the homogeneity `1/2 - κ`**, plus `κ̄ ≥ 0`,
for `0 < θ < κ - κ̄`. -/
theorem gammaGrad_sub_lintegral_enorm_pow_le_kappa (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') (i : Fin 3) {κ κ' θ : ℝ}
    (hκ1 : κ ≤ 1 / 4) (hκ'0 : 0 ≤ κ') (hθ : 0 < θ) (hθκ : θ < κ - κ')
    {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ x y : SpaceTime, torusParabolicSize (y - x) ≤ 1 →
        ∫⁻ ω, ‖gammaGrad N ξ i x y ω - gammaGrad N ξ' i x y ω‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * (max ε ε') ^ θ *
            torusParabolicSize (y - x) ^ (1 / 2 - κ + κ')) ^ q := by
  obtain ⟨C, hC, h⟩ := gammaGrad_sub_lintegral_enorm_pow_le N hρ hρ' i (θ := θ)
    (δ := 2 * κ - 2 * κ' - 2 * θ) hθ (by linarith) (by linarith) (by linarith) hq
  have e : (1 - 2 * θ - (2 * κ - 2 * κ' - 2 * θ)) / 2 = 1 / 2 - κ + κ' := by ring
  rw [e] at h
  exact ⟨C, hC, h⟩

/-- **The `q`-th moment of `v₁^ε - v₁^ε'` at the homogeneity `3/2 - κ`**, plus `κ̄ ≥ 0`,
for `0 < θ < κ - κ̄`. -/
theorem gammaPsiTaylor_sub_lintegral_enorm_pow_le_kappa (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {κ κ' θ : ℝ}
    (hκ1 : κ ≤ 1 / 4) (hκ'0 : 0 ≤ κ') (hθ : 0 < θ) (hθκ : θ < κ - κ')
    {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ (x : SpaceTime) (t : ℝ) (a : Fin 3 → ℝ), parabolicNorm (t, a) ≤ 1 / 2 →
        ∫⁻ ω, ‖gammaPsiTaylor N ξ x t a ω - gammaPsiTaylor N ξ' x t a ω‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * (max ε ε') ^ θ *
            parabolicNorm (t, a) ^ (3 / 2 - κ + κ')) ^ q := by
  obtain ⟨C, hC, h⟩ := gammaPsiTaylor_sub_lintegral_enorm_pow_le N hρ hρ' (θ := θ)
    (δ := 2 * κ - 2 * κ' - 2 * θ) hθ (by linarith) (by linarith) (by linarith) hq
  have e : (3 - 2 * θ - (2 * κ - 2 * κ' - 2 * θ)) / 2 = 3 / 2 - κ + κ' := by ring
  rw [e] at h
  exact ⟨C, hC, h⟩

end RegularityStructures.Phi43

end
