/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ShiftedGammaDeltaSub
public import Phi43.BPHZ.GammaFullKolmogorovInputs
import Mathlib.Tactic

/-!
# Near/far moments of the shifted `cPsiCube`

For `C` with `C₁ C = hairerWickConstant N ρ ε + s`, `|s| ≤ B`, the parameter
`U = (gammaFullParam N κ C (ξ ω) y x).cPsiCube` is `v₃ + 3 s D` (`gammaFullParam_cPsiCube_shift`),
`D` the increment of `T₀`.  With `d = d(y, x)`, `e = 1/2 - 3κ + κ̄` and every `Q ≥ 1`:

* `d ≤ 1 → ∫⁻ ‖U‖ₑ^Q ≤ ofReal (A d^e)^Q` and `∫⁻ ‖U‖ₑ^Q ≤ ofReal A'^Q`
  (`gammaFull_cPsiCubeShift_near_far`);
* for two models, with `M = (ε ∨ ε')^θ + |s - s'|`:
  `d ≤ 1 → ∫⁻ ‖U - U'‖ₑ^Q ≤ ofReal (A M d^e)^Q` and `∫⁻ ‖U - U'‖ₑ^Q ≤ ofReal (A' M)^Q`
  (`gammaFull_cPsiCubeShift_sub_near_far`).
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **Near/far moments of the shifted `cPsiCube`.** -/
theorem gammaFull_cPsiCubeShift_near_far (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) {κ : Kappa} {κbar : ℝ} (hκb0 : 0 ≤ κbar) (hκb : κbar ≤ κ.1 / 2)
    {Q : ℕ} (hQ : 1 ≤ Q) {B : ℝ} (hB : 0 ≤ B) :
    ∃ A A' : ℝ, 0 ≤ A ∧ 0 ≤ A' ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}
      {C : RenormalisationConstants} {s : ℝ}, |s| ≤ B →
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      C₁ C = hairerWickConstant N ρ ε + s → (∀ ω, Statements.HasPhi43NoiseGrowth (ξ ω)) →
      ∀ x y : ParabolicSpace,
        (parabolicSemigroup.scaleDist y x ≤ 1 →
          ∫⁻ ω, ‖(gammaFullParam N κ C (ξ ω) y x).cPsiCube‖ₑ ^ Q ∂P ≤
            ENNReal.ofReal (A * parabolicSemigroup.scaleDist y x ^
              (1 / 2 - 3 * κ.1 + κbar)) ^ Q) ∧
        ∫⁻ ω, ‖(gammaFullParam N κ C (ξ ω) y x).cPsiCube‖ₑ ^ Q ∂P ≤ ENNReal.ofReal A' ^ Q := by
  have hk0 : 0 < κ.1 := κ.2.1
  have hk1 : κ.1 < 1 / 16 := κ.2.2
  obtain ⟨Cn, hCn, hn⟩ := gammaWickCube_lintegral_enorm_pow_le_kappa N hρ hk0 (by linarith) hκb0 hκb hQ
  obtain ⟨Cf, hCf, hf⟩ := gammaWickCube_lintegral_enorm_pow_le_uniform.{u} N hρ hQ
  obtain ⟨Dn, Df, hDn, hDf, hD⟩ := gammaFull_convIncr_lintegral_le.{u} N hρ hκb0 hκb hQ (κ := κ)
  refine ⟨Cn + 3 * B * Dn, Cf + 3 * B * Df, by positivity, by positivity, ?_⟩
  intro Ω _ P W ε ξ C s hs hW hε hξ hC hgr x y
  have := hW.isProbabilityMeasure
  have hd0 := parabolicSemigroup.scaleDist_nonneg y x
  have ht := torusParabolicSize_spaceTimeProj_sub_le y x
  have ht0 := torusParabolicSize_nonneg (spaceTimeProj y - spaceTimeProj x)
  have hm3 := measurable_gammaWickCube_omega N hξ (spaceTimeProj x) (spaceTimeProj y)
  have hmD : Measurable fun ω => gammaFullConv N ξ (spaceTimeProj x) ω -
      gammaFullConv N ξ (spaceTimeProj y) ω := by
    refine Measurable.sub ?_ ?_ <;>
    exact measurable_integral_mul_field (measurable_hairerPsiField_uncurry N hξ)
      ((measurable_constantsComparison_hairerKernelTorus N).comp
        (measurable_const.sub measurable_id))
  have e : ∀ ω, (gammaFullParam N κ C (ξ ω) y x).cPsiCube =
      gammaWickCube N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω +
        3 * s * (gammaFullConv N ξ (spaceTimeProj x) ω - gammaFullConv N ξ (spaceTimeProj y) ω) :=
    fun ω => gammaFullParam_cPsiCube_shift hC (hξ.1 ω) (hgr ω) y x
  simp_rw [e]
  have h3s : |3 * s| ≤ 3 * B := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    linarith
  obtain ⟨hDnear, hDfar⟩ := hD hW hε hξ x y
  refine ⟨fun h1 => ?_, ?_⟩
  · have hv : ∫⁻ ω, ‖gammaWickCube N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω‖ₑ ^ Q ∂P ≤
        ENNReal.ofReal (Cn * parabolicSemigroup.scaleDist y x ^ (1 / 2 - 3 * κ.1 + κbar)) ^ Q := by
      have hn' := hn hW hε hξ _ _ (ht.trans h1)
      rw [← mul_one Cn] at hn'
      have h := gammaFull_rpow_mono (Cn := Cn) (M := 1) (t := torusParabolicSize
        (spaceTimeProj y - spaceTimeProj x)) (d := parabolicSemigroup.scaleDist y x)
        (by rw [mul_one]; exact hCn) ht ht0 (by linarith) hn'
      rwa [mul_one] at h
    have hDm := lintegral_enorm_pow_const_mul_le (3 * s) (hDnear h1)
    have hsum := lintegral_enorm_pow_add_le hQ hm3.aestronglyMeasurable
      (hmD.const_mul (3 * s)).aestronglyMeasurable hv hDm
      (mul_nonneg hCn (Real.rpow_nonneg hd0 _))
      (mul_nonneg (abs_nonneg _) (mul_nonneg hDn (Real.rpow_nonneg hd0 _)))
    refine lintegral_enorm_pow_mono hsum ?_
    have hp := Real.rpow_nonneg hd0 (1 / 2 - 3 * κ.1 + κbar)
    nlinarith [mul_le_mul_of_nonneg_right h3s (mul_nonneg hDn hp)]
  · have hDm := lintegral_enorm_pow_const_mul_le (3 * s) hDfar
    have hsum := lintegral_enorm_pow_add_le hQ hm3.aestronglyMeasurable
      (hmD.const_mul (3 * s)).aestronglyMeasurable (hf hW hε hξ _ _) hDm hCf
      (mul_nonneg (abs_nonneg _) hDf)
    refine lintegral_enorm_pow_mono hsum ?_
    nlinarith [mul_le_mul_of_nonneg_right h3s hDf]

end RegularityStructures.Phi43

end
