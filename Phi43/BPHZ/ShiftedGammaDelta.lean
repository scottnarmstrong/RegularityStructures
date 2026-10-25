/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ShiftedGammaPath
public import Phi43.BPHZ.GammaFullParamMomentSub
public import Phi43.BPHZ.GammaFullUniform
import Mathlib.Tactic

/-!
# Moments of the increment of `I(Ψ)`

Let `D(x, y) = T₀(proj x) - T₀(proj y)` with `T₀ = gammaFullConv` the pathwise convolution
`K ∗ Ψ`.  With `d = d(y, x)` and `e = 1/2 - 3κ + κ̄`:

* near (`d ≤ 1`): `∫⁻ ‖D‖ₑ^q ≤ ofReal (A d^e)^q`, far: `∫⁻ ‖D‖ₑ^q ≤ ofReal A'^q`
  (`gammaFull_convIncr_lintegral_le`);
* for two models: the same with the factor `(ε ∨ ε')^θ` for `D - D'`
  (`gammaFull_convIncr_sub_lintegral_le`).

The near bound uses `D = -cPsi + ∑ᵢ relCoordᵢ Tᵢ(x)` (`gammaFullConv_sub_eq`), the far bound the
uniform moments of `T₀`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem sd_rpow_le {d a e : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (he : 0 ≤ e) (hae : e ≤ a) :
    d ^ a ≤ d ^ e :=
  Real.rpow_le_rpow_of_exponent_ge' hd0 hd1 he hae

private theorem sd_self_le {d e : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (he : 0 ≤ e) (he1 : e ≤ 1) :
    d ≤ d ^ e := by
  have := sd_rpow_le hd0 hd1 he he1
  rwa [Real.rpow_one] at this

/-- **Moments of the increment of `T₀ = K ∗ Ψ`.** -/
theorem gammaFull_convIncr_lintegral_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ)
    {κ : Kappa} {κbar : ℝ} (hκb0 : 0 ≤ κbar) (hκb : κbar ≤ κ.1 / 2) {q : ℕ} (hq : 1 ≤ q) :
    ∃ A A' : ℝ, 0 ≤ A ∧ 0 ≤ A' ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ x y : ParabolicSpace,
        (parabolicSemigroup.scaleDist y x ≤ 1 →
          ∫⁻ ω, ‖gammaFullConv N ξ (spaceTimeProj x) ω - gammaFullConv N ξ (spaceTimeProj y) ω‖ₑ ^ q
              ∂P ≤
            ENNReal.ofReal (A * parabolicSemigroup.scaleDist y x ^
              (1 / 2 - 3 * κ.1 + κbar)) ^ q) ∧
        ∫⁻ ω, ‖gammaFullConv N ξ (spaceTimeProj x) ω - gammaFullConv N ξ (spaceTimeProj y) ω‖ₑ ^ q
            ∂P ≤ ENNReal.ofReal A' ^ q := by
  have hk0 : 0 < κ.1 := κ.2.1
  have hk1 : κ.1 < 1 / 16 := κ.2.2
  obtain ⟨C1, hC1, h1⟩ := gammaFull_cPsi_lintegral_le N hρ hκb0 hκb hq (κ := κ)
  obtain ⟨C0, hC0, h0⟩ := gammaFull_conv_lintegral_le.{u} N hρ hq
  obtain ⟨Cg, hCg, hg⟩ := gammaFull_grad_lintegral_le.{u} N hρ hq
  refine ⟨C1 + 3 * Cg, 2 * C0, by positivity, by positivity, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ x y
  have := hW.isProbabilityMeasure
  have hm0 : ∀ z, Measurable fun ω => gammaFullConv N ξ z ω := fun z =>
    measurable_integral_mul_field (measurable_hairerPsiField_uncurry N hξ)
      ((measurable_constantsComparison_hairerKernelTorus N).comp
        (measurable_const.sub measurable_id))
  have hm1 : ∀ i z, Measurable fun ω => gammaFullGrad N ξ i z ω := fun i z =>
    measurable_integral_mul_field (measurable_hairerPsiField_uncurry N hξ)
      ((measurable_hairerKernelTorusGrad N i).comp (measurable_const.sub measurable_id))
  have hD : ∀ ω, gammaFullConv N ξ (spaceTimeProj x) ω - gammaFullConv N ξ (spaceTimeProj y) ω =
      -(gammaFullParam N κ (0 : RenormalisationConstants) (ξ ω) y x).cPsi +
        (CanonicalData.relCoord y x (0 : Fin 3).succ * gammaFullGrad N ξ 0 (spaceTimeProj x) ω +
          CanonicalData.relCoord y x (1 : Fin 3).succ * gammaFullGrad N ξ 1 (spaceTimeProj x) ω +
          CanonicalData.relCoord y x (2 : Fin 3).succ * gammaFullGrad N ξ 2 (spaceTimeProj x) ω) :=
    fun ω => by rw [gammaFullConv_sub_eq (hξ.1 ω), Fin.sum_univ_three]
  refine ⟨fun hd1 => ?_, ?_⟩
  · set d := parabolicSemigroup.scaleDist y x with hd
    have hd0 : 0 ≤ d := parabolicSemigroup.scaleDist_nonneg y x
    have he0 : 0 ≤ 1 / 2 - 3 * κ.1 + κbar := by linarith
    have he1 : 1 / 2 - 3 * κ.1 + κbar ≤ 1 := by linarith
    have hmk : ∀ k : Fin 3, Measurable fun ω => CanonicalData.relCoord y x k.succ *
        gammaFullGrad N ξ k (spaceTimeProj x) ω := fun k => (hm1 k _).const_mul _
    have hgk : ∀ k : Fin 3, ∫⁻ ω, ‖CanonicalData.relCoord y x k.succ *
        gammaFullGrad N ξ k (spaceTimeProj x) ω‖ₑ ^ q ∂P ≤
        ENNReal.ofReal (Cg * d ^ (1 / 2 - 3 * κ.1 + κbar)) ^ q := fun k =>
      lintegral_enorm_pow_mono (lintegral_enorm_pow_const_mul_le _ (hg hW hε hξ k _))
        (by
          have := abs_relCoord_succ_le y x k
          have h2 := sd_self_le hd0 hd1 he0 he1
          nlinarith [mul_le_mul this h2 hd0 hd0, mul_nonneg hd0 hCg, abs_nonneg
            (CanonicalData.relCoord y x k.succ)])
    have hnn : 0 ≤ Cg * d ^ (1 / 2 - 3 * κ.1 + κbar) :=
      mul_nonneg hCg (Real.rpow_nonneg hd0 _)
    have hS := lintegral_enorm_pow_add_le hq
      (((hmk 0).add (hmk 1)).aestronglyMeasurable) (hmk 2).aestronglyMeasurable
      (lintegral_enorm_pow_add_le hq (hmk 0).aestronglyMeasurable (hmk 1).aestronglyMeasurable
        (hgk 0) (hgk 1) hnn hnn) (hgk 2) (add_nonneg hnn hnn) hnn
    have hcm : Measurable fun ω =>
        (gammaFullParam N κ (0 : RenormalisationConstants) (ξ ω) y x).cPsi := by
      have e : ∀ ω, (gammaFullParam N κ (0 : RenormalisationConstants) (ξ ω) y x).cPsi =
          -(gammaFullConv N ξ (spaceTimeProj x) ω - gammaFullConv N ξ (spaceTimeProj y) ω) +
            (CanonicalData.relCoord y x (0 : Fin 3).succ *
                gammaFullGrad N ξ 0 (spaceTimeProj x) ω +
              CanonicalData.relCoord y x (1 : Fin 3).succ *
                gammaFullGrad N ξ 1 (spaceTimeProj x) ω +
              CanonicalData.relCoord y x (2 : Fin 3).succ *
                gammaFullGrad N ξ 2 (spaceTimeProj x) ω) := fun ω => by
        have := hD ω
        linarith
      simp_rw [e]
      exact (((hm0 _).sub (hm0 _)).neg).add (((hmk 0).add (hmk 1)).add (hmk 2))
    have hc := h1 (C := (0 : RenormalisationConstants)) hW hε hξ x y
    have hc' : ∫⁻ ω, ‖-(gammaFullParam N κ (0 : RenormalisationConstants) (ξ ω) y x).cPsi‖ₑ ^ q
        ∂P ≤ ENNReal.ofReal (C1 * d ^ (3 / 2 - κ.1 + κbar)) ^ q := by
      simpa only [enorm_neg] using hc
    have hsum := lintegral_enorm_pow_add_le hq hcm.neg.aestronglyMeasurable
      ((((hmk 0).add (hmk 1)).add (hmk 2)).aestronglyMeasurable) hc' hS
      (mul_nonneg hC1 (Real.rpow_nonneg hd0 _)) (add_nonneg (add_nonneg hnn hnn) hnn)
    simp_rw [hD]
    refine lintegral_enorm_pow_mono hsum ?_
    have h3 := sd_rpow_le hd0 hd1 he0 (show 1 / 2 - 3 * κ.1 + κbar ≤ 3 / 2 - κ.1 + κbar by
      linarith)
    nlinarith [mul_le_mul_of_nonneg_left h3 hC1, Real.rpow_nonneg hd0 (1 / 2 - 3 * κ.1 + κbar),
      mul_nonneg hCg (Real.rpow_nonneg hd0 (1 / 2 - 3 * κ.1 + κbar))]
  · have hdiff := lintegral_enorm_pow_sub_le hq (hm0 (spaceTimeProj x)).aestronglyMeasurable
      (hm0 (spaceTimeProj y)).aestronglyMeasurable (h0 hW hε hξ _) (h0 hW hε hξ _) hC0 hC0
    exact lintegral_enorm_pow_mono hdiff (by linarith)

end RegularityStructures.Phi43

end
