/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.GammaMomentDiff
public import Phi43.BPHZ.GammaMomentLp
public import RegularityStructures.BPHZ.ChaosLimitMomentsTwoFields
import Mathlib.Tactic

/-!
# All moments of the two-scale differences of `v₂` and `v₃`

For regularised noises `ξ` (mollifier `ρ`, scale `ε`), `ξ'` (mollifier `ρ'`, scale `ε'`) of the same
white noise and every `p ≥ 1`,
the differences `v₂^ε - v₂^ε'` and `v₃^ε - v₃^ε'` have integrable `2p`-th powers and
`E D^(2p) ≤ A (E D²)^p` with `A = A(p)` independent of `N`, `ρ`, `ε`, `ε'`, `x`, `y`
(`gammaWickSq_sub_integrable_pow_le`, `gammaWickCube_sub_integrable_pow_le`).  With the second-moment bounds
of `GammaMomentDiff` this gives the `q`-th moments in Kolmogorov form
(`gammaWickSq_sub_lintegral_enorm_pow_le`, `gammaWickCube_sub_lintegral_enorm_pow_le`).
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- `v₂` is the tested polynomial field `∫ (Ψ² - c_ε) δK`. -/
theorem gammaWickSq_eq_integral_eval {Ω : Type*} (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ)
    (ξ : Ω → SpaceTime → ℝ) (x y : SpaceTime) (ω : Ω) :
    gammaWickSq N ρ ε ξ x y ω = ∫ w, (Polynomial.X ^ 2 - Polynomial.C (hairerWickConstant N ρ ε)
      : Polynomial ℝ).eval (hairerPsiField N ξ ω w) * hairerI2Psi2Kernel N x y w := by
  simp only [gammaWickSq, hairerPsiWickSquare]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp [mul_comm]

/-- `v₃` is the tested polynomial field `∫ (Ψ³ - 3 c_ε Ψ) δK`. -/
theorem gammaWickCube_eq_integral_eval {Ω : Type*} (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ)
    (ξ : Ω → SpaceTime → ℝ) (x y : SpaceTime) (ω : Ω) :
    gammaWickCube N ρ ε ξ x y ω = ∫ w, (Polynomial.X ^ 3 -
      Polynomial.C (3 * hairerWickConstant N ρ ε) * Polynomial.X : Polynomial ℝ).eval
        (hairerPsiField N ξ ω w) * hairerI2Psi2Kernel N x y w := by
  simp only [gammaWickCube, hairerPsiWickCube]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp [mul_comm]

/-- **All moments of `v₂^ε - v₂^ε'`.** -/
theorem gammaWickSq_sub_integrable_pow_le (p : ℕ) (hp : 1 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {ε ε' : ℝ}
      {ξ ξ' : Ω → SpaceTime → ℝ} (N : ℕ), IsMollifier ρ → IsMollifier ρ' → IsWhiteNoise P W →
      0 < ε → 0 < ε' →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' → ∀ x y : SpaceTime,
        Integrable (fun ω => (gammaWickSq N ρ ε ξ x y ω - gammaWickSq N ρ' ε' ξ' x y ω) ^ (2 * p)) P ∧
        ∫ ω, (gammaWickSq N ρ ε ξ x y ω - gammaWickSq N ρ' ε' ξ' x y ω) ^ (2 * p) ∂P ≤
          A * (∫ ω, (gammaWickSq N ρ ε ξ x y ω - gammaWickSq N ρ' ε' ξ' x y ω) ^ 2 ∂P) ^ p := by
  obtain ⟨A, hA0, hA⟩ := integrable_and_integral_pow_two_mul_le_of_polyIntegral_sub.{u} 2 p hp
  refine ⟨A, hA0, fun {Ω _ P W ρ ρ' ε ε' ξ ξ'} N hρ hρ' hW hε hε' hξ hξ' x y => ?_⟩
  obtain ⟨S, hSc, hS0, -, hS⟩ := hairerI2Psi2Kernel_chaos_support N x y 0
  have hdeg : ∀ c : ℝ, (Polynomial.X ^ 2 - Polynomial.C c : Polynomial ℝ).natDegree ≤ 2 :=
    fun c => by compute_degree
  have h := hA hW (continuous_hairerPsiField N hξ.1) (continuous_hairerPsiField N hξ'.1)
    (measurable_hairerPsiField_apply N hξ) (measurable_hairerPsiField_apply N hξ')
    (exists_hairerPsiField_pairing N hρ hε hW hξ) (exists_hairerPsiField_pairing N hρ' hε' hW hξ')
    (V := max (hairerCovariance N ρ ε 0) (hairerCovariance N ρ' ε' 0))
    (fun z => (integral_hairerPsiField_sq_le N hρ hε hW hξ z).trans (le_max_left _ _))
    (fun z => (integral_hairerPsiField_sq_le N hρ' hε' hW hξ' z).trans (le_max_right _ _))
    hSc hS0 (measurable_hairerI2Psi2Kernel N x y) (integrable_hairerI2Psi2Kernel N x y)
    (fun w hw => hS y (by simp) w hw)
    (Polynomial.X ^ 2 - Polynomial.C (hairerWickConstant N ρ ε))
    (Polynomial.X ^ 2 - Polynomial.C (hairerWickConstant N ρ' ε')) (hdeg _) (hdeg _)
  simp only [← gammaWickSq_eq_integral_eval] at h
  exact h

/-- **All moments of `v₃^ε - v₃^ε'`.** -/
theorem gammaWickCube_sub_integrable_pow_le (p : ℕ) (hp : 1 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {ε ε' : ℝ}
      {ξ ξ' : Ω → SpaceTime → ℝ} (N : ℕ), IsMollifier ρ → IsMollifier ρ' → IsWhiteNoise P W →
      0 < ε → 0 < ε' →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' → ∀ x y : SpaceTime,
        Integrable (fun ω => (gammaWickCube N ρ ε ξ x y ω - gammaWickCube N ρ' ε' ξ' x y ω) ^ (2 * p)) P ∧
        ∫ ω, (gammaWickCube N ρ ε ξ x y ω - gammaWickCube N ρ' ε' ξ' x y ω) ^ (2 * p) ∂P ≤
          A * (∫ ω, (gammaWickCube N ρ ε ξ x y ω - gammaWickCube N ρ' ε' ξ' x y ω) ^ 2 ∂P) ^ p := by
  obtain ⟨A, hA0, hA⟩ := integrable_and_integral_pow_two_mul_le_of_polyIntegral_sub.{u} 3 p hp
  refine ⟨A, hA0, fun {Ω _ P W ρ ρ' ε ε' ξ ξ'} N hρ hρ' hW hε hε' hξ hξ' x y => ?_⟩
  obtain ⟨S, hSc, hS0, -, hS⟩ := hairerI2Psi2Kernel_chaos_support N x y 0
  have hdeg : ∀ c : ℝ, (Polynomial.X ^ 3 - Polynomial.C (3 * c) * Polynomial.X :
      Polynomial ℝ).natDegree ≤ 3 := fun c => by compute_degree
  have h := hA hW (continuous_hairerPsiField N hξ.1) (continuous_hairerPsiField N hξ'.1)
    (measurable_hairerPsiField_apply N hξ) (measurable_hairerPsiField_apply N hξ')
    (exists_hairerPsiField_pairing N hρ hε hW hξ) (exists_hairerPsiField_pairing N hρ' hε' hW hξ')
    (V := max (hairerCovariance N ρ ε 0) (hairerCovariance N ρ' ε' 0))
    (fun z => (integral_hairerPsiField_sq_le N hρ hε hW hξ z).trans (le_max_left _ _))
    (fun z => (integral_hairerPsiField_sq_le N hρ' hε' hW hξ' z).trans (le_max_right _ _))
    hSc hS0 (measurable_hairerI2Psi2Kernel N x y) (integrable_hairerI2Psi2Kernel N x y)
    (fun w hw => hS y (by simp) w hw)
    (Polynomial.X ^ 3 - Polynomial.C (3 * hairerWickConstant N ρ ε) * Polynomial.X)
    (Polynomial.X ^ 3 - Polynomial.C (3 * hairerWickConstant N ρ' ε') * Polynomial.X)
    (hdeg _) (hdeg _)
  simp only [← gammaWickCube_eq_integral_eval] at h
  exact h

/-- The arithmetic of the `q`-th moment of a two-scale difference. -/
theorem gammaMoment_lintegral_enorm_pow_le_sub {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : Ω → ℝ} (hY : AEStronglyMeasurable Y P) {q : ℕ} (hq : 1 ≤ q)
    {A C₂ M θ r a t : ℝ} (hA : 0 ≤ A) (hC₂ : 0 ≤ C₂) (hM : 0 ≤ M) (hr : 0 ≤ r)
    (ht : t = 2 * a) (hint : Integrable (fun ω => Y ω ^ (2 * q)) P)
    (hmom : ∫ ω, Y ω ^ (2 * q) ∂P ≤ A * (∫ ω, Y ω ^ 2 ∂P) ^ q)
    (h2 : ∫ ω, Y ω ^ 2 ∂P ≤ C₂ * M ^ (2 * θ) * r ^ t) :
    ∫⁻ ω, ‖Y ω‖ₑ ^ q ∂P ≤
      ENNReal.ofReal (max 1 (Real.sqrt A) * Real.sqrt C₂ * M ^ θ * r ^ a) ^ q := by
  have hM2 : (M ^ θ) ^ 2 = M ^ (2 * θ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hM]
    congr 1
    push_cast
    ring
  have hr2 : (r ^ a) ^ 2 = r ^ t := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hr]
    congr 1
    push_cast
    ring
  have hD : (Real.sqrt C₂ * M ^ θ * r ^ a) ^ 2 = C₂ * M ^ (2 * θ) * r ^ t := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hC₂, hM2, hr2]
  have h := Phi43.lintegral_enorm_pow_le_of_moments hY hq hA
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hM _))
      (Real.rpow_nonneg hr _)) hint hmom (hD ▸ h2)
  rwa [← mul_assoc, ← mul_assoc] at h

/-- **The `q`-th moment of `v₂^ε - v₂^ε'`.** -/
theorem gammaWickSq_sub_lintegral_enorm_pow_le (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hδ : 0 < δ)
    (hθδ : 2 * θ + δ ≤ 2) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ x y : SpaceTime, torusParabolicSize (y - x) ≤ 1 →
        ∫⁻ ω, ‖gammaWickSq N ρ ε ξ x y ω - gammaWickSq N ρ' ε' ξ' x y ω‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * (max ε ε') ^ θ *
            torusParabolicSize (y - x) ^ ((2 - 2 * θ - δ) / 2)) ^ q := by
  obtain ⟨C₂, hC₂, h2⟩ := gammaWickSq_sub_second_moment_le N hρ hρ' hθ hθ1 hδ hθδ
  obtain ⟨A, hA0, hA⟩ := gammaWickSq_sub_integrable_pow_le q hq
  refine ⟨max 1 (Real.sqrt A) * Real.sqrt C₂, by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' x y hd
  have := hW.isProbabilityMeasure
  obtain ⟨hi, hm⟩ := hA N hρ hρ' hW hε.1 hε'.1 hξ hξ' x y
  have hmeas : Measurable fun ω => gammaWickSq N ρ ε ξ x y ω - gammaWickSq N ρ' ε' ξ' x y ω :=
    (measurable_integral_mul_field (measurable_hairerPsiWickSquare_uncurry N hξ)
      (measurable_hairerI2Psi2Kernel N x y)).sub
    (measurable_integral_mul_field (measurable_hairerPsiWickSquare_uncurry N hξ')
      (measurable_hairerI2Psi2Kernel N x y))
  exact gammaMoment_lintegral_enorm_pow_le_sub hmeas.aestronglyMeasurable hq hA0 hC₂
    (le_max_of_le_left hε.1.le) (torusParabolicSize_nonneg _) (by ring) hi hm
    (h2 hW hε hε' hξ hξ' x y hd)

/-- **The `q`-th moment of `v₃^ε - v₃^ε'`.** -/
theorem gammaWickCube_sub_lintegral_enorm_pow_le (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {θ δ : ℝ} (hθ : 0 < θ) (hδ : 0 < δ) (hθδ : 2 * θ + δ ≤ 1)
    {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ x y : SpaceTime, torusParabolicSize (y - x) ≤ 1 →
        ∫⁻ ω, ‖gammaWickCube N ρ ε ξ x y ω - gammaWickCube N ρ' ε' ξ' x y ω‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * (max ε ε') ^ θ *
            torusParabolicSize (y - x) ^ ((1 - 2 * θ - δ) / 2)) ^ q := by
  obtain ⟨C₂, hC₂, h2⟩ := gammaWickCube_sub_second_moment_le N hρ hρ' hθ hδ hθδ
  obtain ⟨A, hA0, hA⟩ := gammaWickCube_sub_integrable_pow_le q hq
  refine ⟨max 1 (Real.sqrt A) * Real.sqrt C₂, by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' x y hd
  have := hW.isProbabilityMeasure
  obtain ⟨hi, hm⟩ := hA N hρ hρ' hW hε.1 hε'.1 hξ hξ' x y
  have hmeas : Measurable fun ω => gammaWickCube N ρ ε ξ x y ω - gammaWickCube N ρ' ε' ξ' x y ω :=
    (measurable_integral_mul_field (measurable_hairerPsiWickCube_uncurry N hξ)
      (measurable_hairerI2Psi2Kernel N x y)).sub
    (measurable_integral_mul_field (measurable_hairerPsiWickCube_uncurry N hξ')
      (measurable_hairerI2Psi2Kernel N x y))
  exact gammaMoment_lintegral_enorm_pow_le_sub hmeas.aestronglyMeasurable hq hA0 hC₂
    (le_max_of_le_left hε.1.le) (torusParabolicSize_nonneg _) (by ring) hi hm
    (h2 hW hε hε' hξ hξ' x y hd)

/-- **The `q`-th moment of `v₂^ε - v₂^ε'` at the homogeneity of `I(Ψ²)`**: for `0 < κ ≤ 1/4`,
`0 ≤ κ̄ ≤ κ/2` and `0 < θ ≤ κ`, `∫⁻ ‖v₂^ε - v₂^ε'‖ₑ^q ≤ ofReal (C (ε ∨ ε')^θ d^(1 - 2κ + κ̄))^q`. -/
theorem gammaWickSq_sub_lintegral_enorm_pow_le_kappa (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {κ κ' θ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1 / 4)
    (hκ'0 : 0 ≤ κ') (hκ' : κ' ≤ κ / 2) (hθ : 0 < θ) (hθκ : θ ≤ κ) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ x y : SpaceTime, torusParabolicSize (y - x) ≤ 1 →
        ∫⁻ ω, ‖gammaWickSq N ρ ε ξ x y ω - gammaWickSq N ρ' ε' ξ' x y ω‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * (max ε ε') ^ θ *
            torusParabolicSize (y - x) ^ (1 - 2 * κ + κ')) ^ q := by
  obtain ⟨C, hC, h⟩ := gammaWickSq_sub_lintegral_enorm_pow_le N hρ hρ' (θ := θ)
    (δ := 4 * κ - 2 * κ' - 2 * θ) hθ (by linarith) (by linarith) (by linarith) hq
  have e : (2 - 2 * θ - (4 * κ - 2 * κ' - 2 * θ)) / 2 = 1 - 2 * κ + κ' := by ring
  rw [e] at h
  exact ⟨C, hC, h⟩

/-- **The `q`-th moment of `v₃^ε - v₃^ε'` at the homogeneity of `I(Ψ³)`**: for `0 < κ ≤ 1/6`,
`0 ≤ κ̄ ≤ κ/2` and `0 < θ ≤ κ`,
`∫⁻ ‖v₃^ε - v₃^ε'‖ₑ^q ≤ ofReal (C (ε ∨ ε')^θ d^(1/2 - 3κ + κ̄))^q`. -/
theorem gammaWickCube_sub_lintegral_enorm_pow_le_kappa (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {κ κ' θ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1 / 6)
    (hκ'0 : 0 ≤ κ') (hκ' : κ' ≤ κ / 2) (hθ : 0 < θ) (hθκ : θ ≤ κ) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ x y : SpaceTime, torusParabolicSize (y - x) ≤ 1 →
        ∫⁻ ω, ‖gammaWickCube N ρ ε ξ x y ω - gammaWickCube N ρ' ε' ξ' x y ω‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * (max ε ε') ^ θ *
            torusParabolicSize (y - x) ^ (1 / 2 - 3 * κ + κ')) ^ q := by
  obtain ⟨C, hC, h⟩ := gammaWickCube_sub_lintegral_enorm_pow_le N hρ hρ' (θ := θ)
    (δ := 6 * κ - 2 * κ' - 2 * θ) hθ (by linarith) (by linarith) hq
  have e : (1 - 2 * θ - (6 * κ - 2 * κ' - 2 * θ)) / 2 = 1 / 2 - 3 * κ + κ' := by ring
  rw [e] at h
  exact ⟨C, hC, h⟩

end RegularityStructures.Phi43

end
