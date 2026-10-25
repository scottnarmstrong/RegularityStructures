/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ShiftedGammaCube
import Mathlib.Tactic

/-!
# Near/far moments of the difference of two shifted `cPsiCube`

For two models with constants `C`, `C'`, `C₁ C = hairerWickConstant N ρ ε + s`,
`C₁ C' = hairerWickConstant N ρ' ε' + s'`, `|s|, |s'| ≤ B`, and
`M = (ε ∨ ε')^θ + |s - s'|`, the difference `U - U'` of the `cPsiCube` parameters satisfies
`U - U' = (v₃ - v₃') + 3 (s - s') D + 3 s' (D - D')`, whence
`d ≤ 1 → ∫⁻ ‖U - U'‖ₑ^Q ≤ ofReal (A M d^e)^Q` and `∫⁻ ‖U - U'‖ₑ^Q ≤ ofReal (A' M)^Q`
(`gammaFull_cPsiCubeShift_sub_near_far`).
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **Near/far moments of the difference of two shifted `cPsiCube`.** -/
theorem gammaFull_cPsiCubeShift_sub_near_far (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {κ : Kappa} {κbar θ : ℝ} (hκb0 : 0 ≤ κbar)
    (hκb : κbar ≤ κ.1 / 2) (hθ : 0 < θ) (hθκ : θ < κ.1 - κbar) {Q : ℕ} (hQ : 1 ≤ Q) {B : ℝ}
    (hB : 0 ≤ B) :
    ∃ A A' : ℝ, 0 ≤ A ∧ 0 ≤ A' ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ}
      {C C' : RenormalisationConstants} {s s' : ℝ}, |s| ≤ B → |s'| ≤ B →
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      C₁ C = hairerWickConstant N ρ ε + s → C₁ C' = hairerWickConstant N ρ' ε' + s' →
      (∀ ω, Statements.HasPhi43NoiseGrowth (ξ ω)) → (∀ ω, Statements.HasPhi43NoiseGrowth (ξ' ω)) →
      ∀ x y : ParabolicSpace,
        (parabolicSemigroup.scaleDist y x ≤ 1 →
          ∫⁻ ω, ‖(gammaFullParam N κ C (ξ ω) y x).cPsiCube -
              (gammaFullParam N κ C' (ξ' ω) y x).cPsiCube‖ₑ ^ Q ∂P ≤
            ENNReal.ofReal (A * ((max ε ε') ^ θ + |s - s'|) * parabolicSemigroup.scaleDist y x ^
              (1 / 2 - 3 * κ.1 + κbar)) ^ Q) ∧
        ∫⁻ ω, ‖(gammaFullParam N κ C (ξ ω) y x).cPsiCube -
            (gammaFullParam N κ C' (ξ' ω) y x).cPsiCube‖ₑ ^ Q ∂P ≤
          ENNReal.ofReal (A' * ((max ε ε') ^ θ + |s - s'|)) ^ Q := by
  have hk0 : 0 < κ.1 := κ.2.1
  have hk1 : κ.1 < 1 / 16 := κ.2.2
  have hθ1 : θ ≤ 1 / 4 := by linarith
  obtain ⟨Vn, hVn, hvn⟩ := gammaWickCube_sub_lintegral_enorm_pow_le_kappa N hρ hρ' hk0 (by linarith)
    hκb0 hκb hθ (by linarith) hQ
  obtain ⟨Vf, hVf, hvf⟩ := gammaWickCube_sub_lintegral_enorm_pow_le_uniform.{u} N hρ hρ' hθ hθ1 hQ
  obtain ⟨Dn, Df, hDn, hDf, hD⟩ := gammaFull_convIncr_lintegral_le.{u} N hρ hκb0 hκb hQ (κ := κ)
  obtain ⟨Sn, Sf, hSn, hSf, hS⟩ := gammaFull_convIncr_sub_lintegral_le.{u} N hρ hρ' hκb0 hθ hθκ
    hQ (κ := κ)
  refine ⟨Vn + 3 * Dn + 3 * B * Sn, Vf + 3 * Df + 3 * B * Sf, by positivity, by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' C C' s s' hs hs' hW hε hε' hξ hξ' hC hC' hgr hgr' x y
  have := hW.isProbabilityMeasure
  have hd0 := parabolicSemigroup.scaleDist_nonneg y x
  have ht := torusParabolicSize_spaceTimeProj_sub_le y x
  have ht0 := torusParabolicSize_nonneg (spaceTimeProj y - spaceTimeProj x)
  have hMx : 0 ≤ (max ε ε') ^ θ := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
  have hMs : 0 ≤ |s - s'| := abs_nonneg _
  have hM : 0 ≤ (max ε ε') ^ θ + |s - s'| := add_nonneg hMx hMs
  have hm3 := measurable_gammaWickCube_omega N hξ (spaceTimeProj x) (spaceTimeProj y)
  have hm3' := measurable_gammaWickCube_omega N hξ' (spaceTimeProj x) (spaceTimeProj y)
  have hmD : ∀ ξ₀ : Ω → SpaceTime → ℝ, (IsRegularisedNoise P W ρ ε ξ₀ ∨
      IsRegularisedNoise P W ρ' ε' ξ₀) → Measurable fun ω =>
      gammaFullConv N ξ₀ (spaceTimeProj x) ω - gammaFullConv N ξ₀ (spaceTimeProj y) ω := by
    intro ξ₀ h
    rcases h with h | h <;>
    · refine Measurable.sub ?_ ?_ <;>
      exact measurable_integral_mul_field (measurable_hairerPsiField_uncurry N h)
        ((measurable_constantsComparison_hairerKernelTorus N).comp
          (measurable_const.sub measurable_id))
  have e : ∀ ω, (gammaFullParam N κ C (ξ ω) y x).cPsiCube -
      (gammaFullParam N κ C' (ξ' ω) y x).cPsiCube =
      (gammaWickCube N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω -
          gammaWickCube N ρ' ε' ξ' (spaceTimeProj x) (spaceTimeProj y) ω) +
        3 * (s - s') * (gammaFullConv N ξ (spaceTimeProj x) ω -
          gammaFullConv N ξ (spaceTimeProj y) ω) +
        3 * s' * ((gammaFullConv N ξ (spaceTimeProj x) ω - gammaFullConv N ξ (spaceTimeProj y) ω) -
          (gammaFullConv N ξ' (spaceTimeProj x) ω - gammaFullConv N ξ' (spaceTimeProj y) ω)) :=
    fun ω => by
      rw [gammaFullParam_cPsiCube_shift hC (hξ.1 ω) (hgr ω),
        gammaFullParam_cPsiCube_shift hC' (hξ'.1 ω) (hgr' ω)]
      ring
  simp_rw [e]
  have h3s : |3 * (s - s')| ≤ 3 * |s - s'| := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  have h3s' : |3 * s'| ≤ 3 * B := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    linarith
  obtain ⟨hDnear, hDfar⟩ := hD hW hε hξ x y
  obtain ⟨hSnear, hSfar⟩ := hS hW hε hε' hξ hξ' x y
  have hm1 := hm3.sub hm3'
  have hm2 := (hmD ξ (Or.inl hξ)).const_mul (3 * (s - s'))
  have hm4 := ((hmD ξ (Or.inl hξ)).sub (hmD ξ' (Or.inr hξ'))).const_mul (3 * s')
  refine ⟨fun h1 => ?_, ?_⟩
  · have hv : ∫⁻ ω, ‖gammaWickCube N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω -
        gammaWickCube N ρ' ε' ξ' (spaceTimeProj x) (spaceTimeProj y) ω‖ₑ ^ Q ∂P ≤
        ENNReal.ofReal (Vn * (max ε ε') ^ θ *
          parabolicSemigroup.scaleDist y x ^ (1 / 2 - 3 * κ.1 + κbar)) ^ Q := by
      have hn' := hvn hW hε hε' hξ hξ' _ _ (ht.trans h1)
      exact gammaFull_rpow_mono (Cn := Vn) (M := (max ε ε') ^ θ) (t := torusParabolicSize
        (spaceTimeProj y - spaceTimeProj x)) (d := parabolicSemigroup.scaleDist y x)
        (mul_nonneg hVn hMx) ht ht0 (by linarith) hn'
    have hDm := lintegral_enorm_pow_const_mul_le (3 * (s - s')) (hDnear h1)
    have hSm := lintegral_enorm_pow_const_mul_le (3 * s') (hSnear h1)
    have hp := Real.rpow_nonneg hd0 (1 / 2 - 3 * κ.1 + κbar)
    have hsum1 := lintegral_enorm_pow_add_le hQ hm1.aestronglyMeasurable hm2.aestronglyMeasurable
      hv hDm (mul_nonneg (mul_nonneg hVn hMx) hp)
      (mul_nonneg (abs_nonneg _) (mul_nonneg hDn hp))
    have hsum2 := lintegral_enorm_pow_add_le hQ (hm1.add hm2).aestronglyMeasurable
      hm4.aestronglyMeasurable hsum1 hSm
      (add_nonneg (mul_nonneg (mul_nonneg hVn hMx) hp)
        (mul_nonneg (abs_nonneg _) (mul_nonneg hDn hp)))
      (mul_nonneg (abs_nonneg _) (mul_nonneg (mul_nonneg hSn hMx) hp))
    refine lintegral_enorm_pow_mono hsum2 ?_
    have a1 := mul_le_mul_of_nonneg_right h3s (mul_nonneg hDn hp)
    have a2 := mul_le_mul_of_nonneg_right h3s' (mul_nonneg (mul_nonneg hSn hMx) hp)
    linarith [mul_nonneg hVn (mul_nonneg hMx hp), mul_nonneg hDn (mul_nonneg hMx hp),
      mul_nonneg hDn (mul_nonneg hMs hp), mul_nonneg hSn (mul_nonneg hMx hp),
      mul_nonneg hVn (mul_nonneg hMs hp), mul_nonneg hSn (mul_nonneg hMs hp),
      mul_nonneg hB (mul_nonneg hSn (mul_nonneg hMs hp)),
      mul_nonneg hB (mul_nonneg hSn (mul_nonneg hMx hp))]
  · have hDm := lintegral_enorm_pow_const_mul_le (3 * (s - s')) hDfar
    have hSm := lintegral_enorm_pow_const_mul_le (3 * s') hSfar
    have hsum1 := lintegral_enorm_pow_add_le hQ hm1.aestronglyMeasurable hm2.aestronglyMeasurable
      (hvf hW hε hε' hξ hξ' _ _) hDm (mul_nonneg hVf hMx)
      (mul_nonneg (abs_nonneg _) hDf)
    have hsum2 := lintegral_enorm_pow_add_le hQ (hm1.add hm2).aestronglyMeasurable
      hm4.aestronglyMeasurable hsum1 hSm
      (add_nonneg (mul_nonneg hVf hMx) (mul_nonneg (abs_nonneg _) hDf))
      (mul_nonneg (abs_nonneg _) (mul_nonneg hSf hMx))
    refine lintegral_enorm_pow_mono hsum2 ?_
    have a1 := mul_le_mul_of_nonneg_right h3s hDf
    have a2 := mul_le_mul_of_nonneg_right h3s' (mul_nonneg hSf hMx)
    linarith [mul_nonneg hVf hMx, mul_nonneg hDf hMx, mul_nonneg hDf hMs,
      mul_nonneg hSf hMx, mul_nonneg hVf hMs, mul_nonneg hSf hMs,
      mul_nonneg hB (mul_nonneg hSf hMs), mul_nonneg hB (mul_nonneg hSf hMx)]

end RegularityStructures.Phi43

end
