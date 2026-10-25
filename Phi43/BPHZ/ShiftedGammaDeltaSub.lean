/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ShiftedGammaDelta
import Mathlib.Tactic

/-!
# Moments of the difference of the increments of `I(Ψ)` for two models

With `D, D'` the increments `T₀(proj x) - T₀(proj y)` of two regularised noises, near (`d ≤ 1`)
`∫⁻ ‖D - D'‖ₑ^q ≤ ofReal (A (ε ∨ ε')^θ d^e)^q`, far `∫⁻ ‖D - D'‖ₑ^q ≤ ofReal (A' (ε ∨ ε')^θ)^q`,
`e = 1/2 - 3κ + κ̄` (`gammaFull_convIncr_sub_lintegral_le`).
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem sds_rpow_le {d a e : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (he : 0 ≤ e) (hae : e ≤ a) :
    d ^ a ≤ d ^ e :=
  Real.rpow_le_rpow_of_exponent_ge' hd0 hd1 he hae

private theorem sds_self_le {d e : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (he : 0 ≤ e) (he1 : e ≤ 1) :
    d ≤ d ^ e := by
  have := sds_rpow_le hd0 hd1 he he1
  rwa [Real.rpow_one] at this

/-- **Moments of the difference of the increments of `T₀`.** -/
theorem gammaFull_convIncr_sub_lintegral_le (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {κ : Kappa} {κbar θ : ℝ} (hκb0 : 0 ≤ κbar)
    (hθ : 0 < θ) (hθκ : θ < κ.1 - κbar) {q : ℕ} (hq : 1 ≤ q) :
    ∃ A A' : ℝ, 0 ≤ A ∧ 0 ≤ A' ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ x y : ParabolicSpace,
        (parabolicSemigroup.scaleDist y x ≤ 1 →
          ∫⁻ ω, ‖(gammaFullConv N ξ (spaceTimeProj x) ω - gammaFullConv N ξ (spaceTimeProj y) ω) -
              (gammaFullConv N ξ' (spaceTimeProj x) ω - gammaFullConv N ξ' (spaceTimeProj y) ω)‖ₑ ^
              q ∂P ≤
            ENNReal.ofReal (A * (max ε ε') ^ θ * parabolicSemigroup.scaleDist y x ^
              (1 / 2 - 3 * κ.1 + κbar)) ^ q) ∧
        ∫⁻ ω, ‖(gammaFullConv N ξ (spaceTimeProj x) ω - gammaFullConv N ξ (spaceTimeProj y) ω) -
            (gammaFullConv N ξ' (spaceTimeProj x) ω - gammaFullConv N ξ' (spaceTimeProj y) ω)‖ₑ ^
            q ∂P ≤ ENNReal.ofReal (A' * (max ε ε') ^ θ) ^ q := by
  have hk0 : 0 < κ.1 := κ.2.1
  have hk1 : κ.1 < 1 / 16 := κ.2.2
  have hθ1 : θ ≤ 1 / 4 := by linarith
  obtain ⟨C1, hC1, h1⟩ := gammaFull_cPsi_sub_lintegral_le N hρ hρ' hκb0 hθ hθκ hq (κ := κ)
  obtain ⟨C0, hC0, h0⟩ := gammaFull_conv_sub_lintegral_le.{u} N hρ hρ' hθ hθ1 hq
  obtain ⟨Cg, hCg, hg⟩ := gammaFull_grad_sub_lintegral_le.{u} N hρ hρ' hθ hθ1 hq
  refine ⟨C1 + 3 * Cg, 2 * C0, by positivity, by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' x y
  have := hW.isProbabilityMeasure
  have hMx : 0 ≤ (max ε ε') ^ θ := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
  have hreg : ∀ ξ₀ : Ω → SpaceTime → ℝ, (IsRegularisedNoise P W ρ ε ξ₀ ∨
      IsRegularisedNoise P W ρ' ε' ξ₀) → (∀ z, Measurable fun ω => gammaFullConv N ξ₀ z ω) ∧
      ∀ i z, Measurable fun ω => gammaFullGrad N ξ₀ i z ω := by
    intro ξ₀ h
    rcases h with h | h
    · exact ⟨fun z => measurable_integral_mul_field (measurable_hairerPsiField_uncurry N h)
        ((measurable_constantsComparison_hairerKernelTorus N).comp
          (measurable_const.sub measurable_id)), fun i z =>
        measurable_integral_mul_field (measurable_hairerPsiField_uncurry N h)
          ((measurable_hairerKernelTorusGrad N i).comp (measurable_const.sub measurable_id))⟩
    · exact ⟨fun z => measurable_integral_mul_field (measurable_hairerPsiField_uncurry N h)
        ((measurable_constantsComparison_hairerKernelTorus N).comp
          (measurable_const.sub measurable_id)), fun i z =>
        measurable_integral_mul_field (measurable_hairerPsiField_uncurry N h)
          ((measurable_hairerKernelTorusGrad N i).comp (measurable_const.sub measurable_id))⟩
  obtain ⟨hm0, hm1⟩ := hreg ξ (Or.inl hξ)
  obtain ⟨hm0', hm1'⟩ := hreg ξ' (Or.inr hξ')
  have hD : ∀ (ξ₀ : Ω → SpaceTime → ℝ) (ω : Ω), IsSmoothOnSpaceTime (ξ₀ ω) →
      gammaFullConv N ξ₀ (spaceTimeProj x) ω - gammaFullConv N ξ₀ (spaceTimeProj y) ω =
      -(gammaFullParam N κ (0 : RenormalisationConstants) (ξ₀ ω) y x).cPsi +
        (CanonicalData.relCoord y x (0 : Fin 3).succ * gammaFullGrad N ξ₀ 0 (spaceTimeProj x) ω +
          CanonicalData.relCoord y x (1 : Fin 3).succ * gammaFullGrad N ξ₀ 1 (spaceTimeProj x) ω +
          CanonicalData.relCoord y x (2 : Fin 3).succ * gammaFullGrad N ξ₀ 2 (spaceTimeProj x) ω) :=
    fun ξ₀ ω hf => by rw [gammaFullConv_sub_eq hf, Fin.sum_univ_three]
  refine ⟨fun hd1 => ?_, ?_⟩
  · set d := parabolicSemigroup.scaleDist y x with hd
    have hd0 : 0 ≤ d := parabolicSemigroup.scaleDist_nonneg y x
    have he0 : 0 ≤ 1 / 2 - 3 * κ.1 + κbar := by linarith
    have he1 : 1 / 2 - 3 * κ.1 + κbar ≤ 1 := by linarith
    have hmk : ∀ k : Fin 3, Measurable fun ω => CanonicalData.relCoord y x k.succ *
        (gammaFullGrad N ξ k (spaceTimeProj x) ω - gammaFullGrad N ξ' k (spaceTimeProj x) ω) :=
      fun k => ((hm1 k _).sub (hm1' k _)).const_mul _
    have hgk : ∀ k : Fin 3, ∫⁻ ω, ‖CanonicalData.relCoord y x k.succ *
        (gammaFullGrad N ξ k (spaceTimeProj x) ω - gammaFullGrad N ξ' k (spaceTimeProj x) ω)‖ₑ ^
        q ∂P ≤ ENNReal.ofReal (Cg * (max ε ε') ^ θ * d ^ (1 / 2 - 3 * κ.1 + κbar)) ^ q :=
      fun k =>
      lintegral_enorm_pow_mono (lintegral_enorm_pow_const_mul_le _ (hg hW hε hε' hξ hξ' k _))
        (by
          have h1 := (abs_relCoord_succ_le y x k).trans (sds_self_le hd0 hd1 he0 he1)
          have h4 : 0 ≤ Cg * (max ε ε') ^ θ := mul_nonneg hCg hMx
          calc |CanonicalData.relCoord y x k.succ| * (Cg * (max ε ε') ^ θ)
              ≤ d ^ (1 / 2 - 3 * κ.1 + κbar) * (Cg * (max ε ε') ^ θ) :=
                mul_le_mul_of_nonneg_right h1 h4
            _ = Cg * (max ε ε') ^ θ * d ^ (1 / 2 - 3 * κ.1 + κbar) := by ring)
    have hnn : 0 ≤ Cg * (max ε ε') ^ θ * d ^ (1 / 2 - 3 * κ.1 + κbar) :=
      mul_nonneg (mul_nonneg hCg hMx) (Real.rpow_nonneg hd0 _)
    have hS := lintegral_enorm_pow_add_le hq
      (((hmk 0).add (hmk 1)).aestronglyMeasurable) (hmk 2).aestronglyMeasurable
      (lintegral_enorm_pow_add_le hq (hmk 0).aestronglyMeasurable (hmk 1).aestronglyMeasurable
        (hgk 0) (hgk 1) hnn hnn) (hgk 2) (add_nonneg hnn hnn) hnn
    have hcm : Measurable fun ω =>
        (gammaFullParam N κ (0 : RenormalisationConstants) (ξ ω) y x).cPsi -
          (gammaFullParam N κ (0 : RenormalisationConstants) (ξ' ω) y x).cPsi := by
      have e : ∀ ω, (gammaFullParam N κ (0 : RenormalisationConstants) (ξ ω) y x).cPsi -
          (gammaFullParam N κ (0 : RenormalisationConstants) (ξ' ω) y x).cPsi =
          -((gammaFullConv N ξ (spaceTimeProj x) ω - gammaFullConv N ξ (spaceTimeProj y) ω) -
            (gammaFullConv N ξ' (spaceTimeProj x) ω - gammaFullConv N ξ' (spaceTimeProj y) ω)) +
          (CanonicalData.relCoord y x (0 : Fin 3).succ *
              (gammaFullGrad N ξ 0 (spaceTimeProj x) ω - gammaFullGrad N ξ' 0 (spaceTimeProj x) ω) +
            CanonicalData.relCoord y x (1 : Fin 3).succ *
              (gammaFullGrad N ξ 1 (spaceTimeProj x) ω - gammaFullGrad N ξ' 1 (spaceTimeProj x) ω) +
            CanonicalData.relCoord y x (2 : Fin 3).succ *
              (gammaFullGrad N ξ 2 (spaceTimeProj x) ω -
                gammaFullGrad N ξ' 2 (spaceTimeProj x) ω)) := fun ω => by
        have a1 := hD ξ ω (hξ.1 ω)
        have a2 := hD ξ' ω (hξ'.1 ω)
        linarith
      simp_rw [e]
      exact ((((hm0 _).sub (hm0 _)).sub ((hm0' _).sub (hm0' _))).neg).add
        (((hmk 0).add (hmk 1)).add (hmk 2))
    have hc := h1 (C := (0 : RenormalisationConstants)) (C' := (0 : RenormalisationConstants))
      hW hε hε' hξ hξ' x y
    have hc' : ∫⁻ ω, ‖-((gammaFullParam N κ (0 : RenormalisationConstants) (ξ ω) y x).cPsi -
        (gammaFullParam N κ (0 : RenormalisationConstants) (ξ' ω) y x).cPsi)‖ₑ ^ q ∂P ≤
        ENNReal.ofReal (C1 * (max ε ε') ^ θ * d ^ (3 / 2 - κ.1 + κbar)) ^ q := by
      simpa only [enorm_neg] using hc
    have hsum := lintegral_enorm_pow_add_le hq hcm.neg.aestronglyMeasurable
      ((((hmk 0).add (hmk 1)).add (hmk 2)).aestronglyMeasurable) hc' hS
      (mul_nonneg (mul_nonneg hC1 hMx) (Real.rpow_nonneg hd0 _))
      (add_nonneg (add_nonneg hnn hnn) hnn)
    have e2 : ∀ ω, (gammaFullConv N ξ (spaceTimeProj x) ω - gammaFullConv N ξ (spaceTimeProj y) ω) -
        (gammaFullConv N ξ' (spaceTimeProj x) ω - gammaFullConv N ξ' (spaceTimeProj y) ω) =
        -((gammaFullParam N κ (0 : RenormalisationConstants) (ξ ω) y x).cPsi -
          (gammaFullParam N κ (0 : RenormalisationConstants) (ξ' ω) y x).cPsi) +
        (CanonicalData.relCoord y x (0 : Fin 3).succ *
            (gammaFullGrad N ξ 0 (spaceTimeProj x) ω - gammaFullGrad N ξ' 0 (spaceTimeProj x) ω) +
          CanonicalData.relCoord y x (1 : Fin 3).succ *
            (gammaFullGrad N ξ 1 (spaceTimeProj x) ω - gammaFullGrad N ξ' 1 (spaceTimeProj x) ω) +
          CanonicalData.relCoord y x (2 : Fin 3).succ *
            (gammaFullGrad N ξ 2 (spaceTimeProj x) ω -
              gammaFullGrad N ξ' 2 (spaceTimeProj x) ω)) := fun ω => by
      have a1 := hD ξ ω (hξ.1 ω)
      have a2 := hD ξ' ω (hξ'.1 ω)
      linarith
    simp_rw [e2]
    refine lintegral_enorm_pow_mono hsum ?_
    have h3 := sds_rpow_le hd0 hd1 he0 (show 1 / 2 - 3 * κ.1 + κbar ≤ 3 / 2 - κ.1 + κbar by
      linarith)
    nlinarith [mul_le_mul_of_nonneg_left h3 (mul_nonneg hC1 hMx),
      Real.rpow_nonneg hd0 (1 / 2 - 3 * κ.1 + κbar),
      mul_nonneg (mul_nonneg hCg hMx) (Real.rpow_nonneg hd0 (1 / 2 - 3 * κ.1 + κbar))]
  · have hA := lintegral_enorm_pow_sub_le hq
      ((hm0 (spaceTimeProj x)).sub (hm0' (spaceTimeProj x))).aestronglyMeasurable
      ((hm0 (spaceTimeProj y)).sub (hm0' (spaceTimeProj y))).aestronglyMeasurable
      (a := C0 * (max ε ε') ^ θ) (b := C0 * (max ε ε') ^ θ)
      (h0 hW hε hε' hξ hξ' (spaceTimeProj x)) (h0 hW hε hε' hξ hξ' (spaceTimeProj y))
      (mul_nonneg hC0 hMx) (mul_nonneg hC0 hMx)
    have e : ∀ ω, (gammaFullConv N ξ (spaceTimeProj x) ω - gammaFullConv N ξ (spaceTimeProj y) ω) -
        (gammaFullConv N ξ' (spaceTimeProj x) ω - gammaFullConv N ξ' (spaceTimeProj y) ω) =
        (gammaFullConv N ξ (spaceTimeProj x) ω - gammaFullConv N ξ' (spaceTimeProj x) ω) -
          (gammaFullConv N ξ (spaceTimeProj y) ω - gammaFullConv N ξ' (spaceTimeProj y) ω) :=
      fun ω => by ring
    simp_rw [e]
    exact lintegral_enorm_pow_mono hA (by nlinarith)

end RegularityStructures.Phi43

end
