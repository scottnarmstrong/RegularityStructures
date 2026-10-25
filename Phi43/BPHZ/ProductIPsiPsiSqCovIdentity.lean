/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductIPsiPsiCovIdentity
public import Phi43.BPHZ.ProductIPsiPsiSqCovSix
public import Phi43.BPHZ.TreeWickSquare
import Mathlib.Tactic

/-!
# The covariance of `Π_x I(Ψ)(Ψ² - c₁)` at two points

With the notation of `ProductIPsiPsiCovIdentity` and `c₁ = hairerWickConstant N ρ ε = Q(0)`,
`E[F(y) F(y')] = 2 B Q(p - p')² + 4 A A' Q(p - p') + 4 R R' Q(p - p')`
(`hairerIPsiPsiSqField_integral_mul`), by Fubini for tested pairs and the Wick-square block.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ} {ξ : Ω → SpaceTime → ℝ}

/-- **Covariance identity for `Π_x I(Ψ)(Ψ² - c₁)`.** -/
theorem hairerIPsiPsiSqField_integral_mul (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ) (x y y' : ParabolicSpace)
    (hA : Integrable (fun w => ipsiTaylorKernel N x y w *
      hairerCovariance N ρ ε (w - spaceTimeProj y)))
    (hA' : Integrable (fun w => ipsiTaylorKernel N x y' w *
      hairerCovariance N ρ ε (w - spaceTimeProj y')))
    (hR : Integrable (fun w => ipsiTaylorKernel N x y w *
      hairerCovariance N ρ ε (w - spaceTimeProj y')))
    (hR' : Integrable (fun w => ipsiTaylorKernel N x y' w *
      hairerCovariance N ρ ε (spaceTimeProj y - w))) :
    ∫ ω, hairerIPsiPsiSqField N ξ (hairerWickConstant N ρ ε) x ω y *
        hairerIPsiPsiSqField N ξ (hairerWickConstant N ρ ε) x ω y' ∂P =
      2 * (∫ ω, hairerIPsiRecentred N ξ ω x y * hairerIPsiRecentred N ξ ω x y' ∂P) *
          hairerCovariance N ρ ε (spaceTimeProj y - spaceTimeProj y') ^ 2 +
      4 * ((∫ w, ipsiTaylorKernel N x y w * hairerCovariance N ρ ε (w - spaceTimeProj y)) *
        (∫ w, ipsiTaylorKernel N x y' w * hairerCovariance N ρ ε (w - spaceTimeProj y')) *
          hairerCovariance N ρ ε (spaceTimeProj y - spaceTimeProj y')) +
      4 * ((∫ w, ipsiTaylorKernel N x y w * hairerCovariance N ρ ε (w - spaceTimeProj y')) *
        (∫ w, ipsiTaylorKernel N x y' w * hairerCovariance N ρ ε (spaceTimeProj y - w)) *
          hairerCovariance N ρ ε (spaceTimeProj y - spaceTimeProj y')) := by
  have := hW.isProbabilityMeasure
  set Q := hairerCovariance N ρ ε with hQ
  set p := spaceTimeProj y with hp
  set p' := spaceTimeProj y' with hp'
  have hwc : hairerWickConstant N ρ ε = Q 0 := hairerWickConstant_eq_covariance_zero N ρ ε
  have hY := measurable_hairerPsiField_uncurry N hξ
  have mΨ : ∀ z, Measurable (fun ω => hairerPsiField N ξ ω z) := fun z =>
    measurable_hairerPsiField_apply N hξ z
  have mS : ∀ z, Measurable (fun ω => hairerPsiField N ξ ω z ^ 2 - Q 0) := fun z =>
    ((mΨ z).pow_const 2).sub_const _
  have hblock := fun q : SpaceTime × SpaceTime =>
    hairerPsiField_wick_block_abs_le N hρ hε hW hξ q.1 p q.2 p'
  have hi : ∀ q : SpaceTime × SpaceTime,
      Integrable (fun ω => hairerPsiField N ξ ω q.1 * (hairerPsiField N ξ ω p ^ 2 - Q 0) *
        (hairerPsiField N ξ ω q.2 * (hairerPsiField N ξ ω p' ^ 2 - Q 0))) P := fun q => by
    refine (hblock q).1.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only; ring
  have hM : ∀ q : SpaceTime × SpaceTime,
      ∫ ω, |hairerPsiField N ξ ω q.1 * (hairerPsiField N ξ ω p ^ 2 - Q 0) *
        (hairerPsiField N ξ ω q.2 * (hairerPsiField N ξ ω p' ^ 2 - Q 0))| ∂P ≤
      (3 * Q 0 ^ 2 + 60 * Q 0 ^ 4 + 3 * Q 0 ^ 2 + 60 * Q 0 ^ 4) / 4 := fun q => by
    refine le_trans (le_of_eq (integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)))
      (hblock q).2
    simp only; congr 1; ring
  have hmain := integral_testedPair_eq (P := P)
    (a := fun ω => hairerPsiField N ξ ω p ^ 2 - Q 0)
    (b := fun ω => hairerPsiField N ξ ω p' ^ 2 - Q 0) hY hY (mS p) (mS p')
    (integrable_ipsiTaylorKernel N x y) (integrable_ipsiTaylorKernel N x y') hi hM
  have hexp := integrable_testedPair_expectation (P := P)
    (a := fun ω => hairerPsiField N ξ ω p ^ 2 - Q 0)
    (b := fun ω => hairerPsiField N ξ ω p' ^ 2 - Q 0) hY hY (mS p) (mS p')
    (integrable_ipsiTaylorKernel N x y) (integrable_ipsiTaylorKernel N x y') hi hM
  have e1 : ∀ ω, hairerIPsiPsiSqField N ξ (hairerWickConstant N ρ ε) x ω y *
      hairerIPsiPsiSqField N ξ (hairerWickConstant N ρ ε) x ω y' =
      (∫ w, ipsiTaylorKernel N x y w * hairerPsiField N ξ ω w) *
        (hairerPsiField N ξ ω p ^ 2 - Q 0) *
        ((∫ w, ipsiTaylorKernel N x y' w * hairerPsiField N ξ ω w) *
          (hairerPsiField N ξ ω p' ^ 2 - Q 0)) := fun ω => by
    unfold hairerIPsiPsiSqField hairerTreePsiSq
    rw [hairerIPsiRecentred_eq_integral N (hξ.1 ω), hairerIPsiRecentred_eq_integral N (hξ.1 ω), hwc]
  simp_rw [e1]
  rw [hmain]
  have hpt : ∀ q : SpaceTime × SpaceTime,
      ipsiTaylorKernel N x y q.1 * ipsiTaylorKernel N x y' q.2 *
        ∫ ω, hairerPsiField N ξ ω q.1 * (hairerPsiField N ξ ω p ^ 2 - Q 0) *
          (hairerPsiField N ξ ω q.2 * (hairerPsiField N ξ ω p' ^ 2 - Q 0)) ∂P =
      4 * Q (p - p') * ((ipsiTaylorKernel N x y q.1 * Q (q.1 - p)) *
        (ipsiTaylorKernel N x y' q.2 * Q (q.2 - p'))) +
      2 * Q (p - p') ^ 2 * (ipsiTaylorKernel N x y q.1 * ipsiTaylorKernel N x y' q.2 *
        Q (q.1 - q.2)) +
      4 * Q (p - p') * ((ipsiTaylorKernel N x y q.1 * Q (q.1 - p')) *
        (ipsiTaylorKernel N x y' q.2 * Q (p - q.2))) := fun q => by
    have h4 := hairerPsiField_wick_block N hρ hε hW hξ q.1 p q.2 p'
    have : ∫ ω, hairerPsiField N ξ ω q.1 * (hairerPsiField N ξ ω p ^ 2 - Q 0) *
        (hairerPsiField N ξ ω q.2 * (hairerPsiField N ξ ω p' ^ 2 - Q 0)) ∂P =
        ∫ ω, hairerPsiField N ξ ω q.1 * (hairerPsiField N ξ ω p ^ 2 - Q 0) *
          hairerPsiField N ξ ω q.2 * (hairerPsiField N ξ ω p' ^ 2 - Q 0) ∂P :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => by simp only; ring)
    rw [this, h4]
    ring
  simp_rw [hpt]
  have i1 : Integrable (fun q : SpaceTime × SpaceTime =>
      4 * Q (p - p') * ((ipsiTaylorKernel N x y q.1 * Q (q.1 - p)) *
        (ipsiTaylorKernel N x y' q.2 * Q (q.2 - p')))) := (hA.mul_prod hA').const_mul _
  have i3 : Integrable (fun q : SpaceTime × SpaceTime =>
      4 * Q (p - p') * ((ipsiTaylorKernel N x y q.1 * Q (q.1 - p')) *
        (ipsiTaylorKernel N x y' q.2 * Q (p - q.2)))) := (hR.mul_prod hR').const_mul _
  have iT : Integrable (fun q : SpaceTime × SpaceTime =>
      ipsiTaylorKernel N x y q.1 * ipsiTaylorKernel N x y' q.2 *
        ∫ ω, hairerPsiField N ξ ω q.1 * (hairerPsiField N ξ ω p ^ 2 - Q 0) *
          (hairerPsiField N ξ ω q.2 * (hairerPsiField N ξ ω p' ^ 2 - Q 0)) ∂P) := hexp
  simp_rw [hpt] at iT
  have i2 : Integrable (fun q : SpaceTime × SpaceTime =>
      2 * Q (p - p') ^ 2 * (ipsiTaylorKernel N x y q.1 * ipsiTaylorKernel N x y' q.2 *
        Q (q.1 - q.2))) := by
    refine ((iT.sub i1).sub i3).congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [Pi.sub_apply]; ring
  have i12 : Integrable (fun q : SpaceTime × SpaceTime =>
      4 * Q (p - p') * ((ipsiTaylorKernel N x y q.1 * Q (q.1 - p)) *
        (ipsiTaylorKernel N x y' q.2 * Q (q.2 - p'))) +
      2 * Q (p - p') ^ 2 * (ipsiTaylorKernel N x y q.1 * ipsiTaylorKernel N x y' q.2 *
        Q (q.1 - q.2))) := i1.add i2
  have j1 : ∫ q : SpaceTime × SpaceTime, (ipsiTaylorKernel N x y q.1 * Q (q.1 - p)) *
      (ipsiTaylorKernel N x y' q.2 * Q (q.2 - p')) =
      (∫ w, ipsiTaylorKernel N x y w * Q (w - p)) *
        ∫ w, ipsiTaylorKernel N x y' w * Q (w - p') :=
    integral_prod_mul (μ := (volume : Measure SpaceTime)) (ν := volume)
      (fun w => ipsiTaylorKernel N x y w * Q (w - p))
      (fun w => ipsiTaylorKernel N x y' w * Q (w - p'))
  have j3 : ∫ q : SpaceTime × SpaceTime, (ipsiTaylorKernel N x y q.1 * Q (q.1 - p')) *
      (ipsiTaylorKernel N x y' q.2 * Q (p - q.2)) =
      (∫ w, ipsiTaylorKernel N x y w * Q (w - p')) *
        ∫ w, ipsiTaylorKernel N x y' w * Q (p - w) :=
    integral_prod_mul (μ := (volume : Measure SpaceTime)) (ν := volume)
      (fun w => ipsiTaylorKernel N x y w * Q (w - p'))
      (fun w => ipsiTaylorKernel N x y' w * Q (p - w))
  rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
    integral_const_mul, j1, j3, ← hairerIPsiRecentred_integral_mul N hρ hε hW hξ x y y']
  ring

end RegularityStructures.Phi43

end
