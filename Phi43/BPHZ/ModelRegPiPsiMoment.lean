/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ModelRegPiPsi
public import Phi43.BPHZ.SemigroupTestPsi
public import RegularityStructures.Abstract.Model
public import RegularityStructures.BPHZ.ChaosLimitMomentsTruncationAE

/-!
# `q`-th moment of `Q_t Π_x Ψ (x)` for the random models, in the form of the Kolmogorov criterion

`regPi_psi_lintegral_enorm_pow_le`: for the models `Z ω` that are almost surely
`IsPhi43ModelOf N κ (ξ ω) (c_ε, C₂) (Z ω)` with `ξ` a regularised noise,
`∫⁻ ω, ‖(Z ω).regPi x (Pi.single Ψ 1) t x‖ₑ ^ q ≤ ofReal (C * t ^ ((deg Ψ + κ̄) / 4)) ^ q`
for every `t ∈ (0, 1]`, `x`, `ε ∈ (0, 1]`, where `κ̄ ≤ κ`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures RegularityStructures.Phi43

/-- The power comparison `√C t^(-1/8) ≤ C' t^((deg Ψ + κ̄)/4)` used for `Ψ`. -/
theorem psi_rpow_exponent_le (κ : Kappa) {κbar : ℝ} (hκbar : κbar ≤ κ.1) {t : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) :
    t ^ (-(1 / 8 : ℝ)) ≤
      t ^ (((phi43RegularityStructure κ).deg Symbol.psi + κbar) / parabolicSemigroup.order) := by
  refine Real.rpow_le_rpow_of_exponent_ge ht ht1 ?_
  show _ ≤ -(1 / 8 : ℝ)
  have h : parabolicSemigroup.order = 4 := rfl
  rw [h, phi43RegularityStructure_deg]
  simp only [homogeneity]
  linarith

/-- **`q`-th moment of the regularised `Ψ`-coordinate of the random models.**  Uniform in
`ε ∈ (0, 1]`, `t ∈ (0, 1]`, the base point `x`, the noise and the models. -/
theorem regPi_psi_lintegral_enorm_pow_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (κ : Kappa) {κbar : ℝ} (hκbar : κbar ≤ κ.1) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}
      (Z : Ω → Model (phi43RegularityStructure κ) parabolicSemigroup),
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      (∀ᵐ ω ∂P, Statements.IsPhi43ModelOf N κ (ξ ω)
        ((hairerWickConstant N ρ ε, hairerSunsetConstant N ρ ε) : RenormalisationConstants)
        (Z ω)) →
      ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
        ∫⁻ ω, ‖(Z ω).regPi x (Pi.single Symbol.psi 1) t x‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * t ^ (((phi43RegularityStructure κ).deg Symbol.psi + κbar) /
            parabolicSemigroup.order)) ^ q := by
  obtain ⟨C₀, hC₀, h2⟩ := hairerPsiField_semigroupPeriodised_second_moment_le N hρ
  obtain ⟨A, hA, hAm⟩ := hairerPsiField_semigroupPeriodised_integrable_pow_le.{u} q hq
  refine ⟨max 1 (Real.sqrt A) * Real.sqrt C₀, by positivity, ?_⟩
  intro Ω _ P W ε ξ Z hW hε hξ hZ t ht x
  have := hW.isProbabilityMeasure
  obtain ⟨ht0, ht1⟩ := ht
  set Yp : Ω → ℝ := fun ω => ∫ w, hairerPsiField N ξ ω w * semigroupPeriodised t x w with hYp
  have hae : (fun ω => (Z ω).regPi x (Pi.single Symbol.psi 1) t x) =ᵐ[P]
      fun ω => ∫ u : SpaceTime, semigroupPeriodised t x u * hairerPsiField N ξ ω u :=
    ae_regPi_single_psi_eq hξ hZ ht0 x (by
      filter_upwards [hairerPsiField_kernel_integrable_ae N hρ hε.1 hW hξ ht0 x] with ω hω
      exact hω)
  have hYeq : ∀ ω, ∫ u : SpaceTime, semigroupPeriodised t x u * hairerPsiField N ξ ω u = Yp ω :=
    fun ω => integral_congr_ae (Filter.Eventually.of_forall fun _ => mul_comm _ _)
  have hYpm : AEStronglyMeasurable Yp P := by
    have h := measurable_integral_mul_field (measurable_hairerPsiField_uncurry N hξ)
      (measurable_semigroupPeriodised t x)
    have e : Yp = fun ω => ∫ u : SpaceTime, semigroupPeriodised t x u * hairerPsiField N ξ ω u :=
      funext fun ω => (hYeq ω).symm
    rw [e]
    exact h.aestronglyMeasurable
  obtain ⟨hint, hmom⟩ := hAm N hρ hW hε.1 hξ ht0 x
  have hsec := h2 hW hε hξ ht0 ht1 x
  simp only [sq_abs] at hsec
  set D : ℝ := Real.sqrt C₀ * t ^ (-(1 / 8 : ℝ)) with hD
  have hD0 : 0 ≤ D := by positivity
  have hD2 : D ^ 2 = C₀ * (t ^ (1 / 4 : ℝ)) ^ (-(1 : ℝ)) := by
    rw [hD, mul_pow, Real.sq_sqrt hC₀, ← Real.rpow_mul ht0.le, ← Real.rpow_natCast,
      ← Real.rpow_mul ht0.le]
    norm_num
  have h2m : ∫ ω, Yp ω ^ 2 ∂P ≤ D ^ 2 := by rw [hD2]; exact hsec
  calc ∫⁻ ω, ‖(Z ω).regPi x (Pi.single Symbol.psi 1) t x‖ₑ ^ q ∂P
      = ∫⁻ ω, ‖Yp ω‖ₑ ^ q ∂P :=
        lintegral_congr_ae (hae.mono fun ω h => congrArg (fun r : ℝ => ‖r‖ₑ ^ q) (h.trans (hYeq ω)))
    _ ≤ ENNReal.ofReal (max 1 (Real.sqrt A) * D) ^ q :=
        lintegral_enorm_pow_le_of_moments hYpm hq hA hD0 hint hmom h2m
    _ ≤ _ := by
        refine pow_le_pow_left' (ENNReal.ofReal_le_ofReal ?_) q
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (psi_rpow_exponent_le κ hκbar ht0 ht1)
            (Real.sqrt_nonneg _)) (by positivity)

end RegularityStructures.Phi43

end
