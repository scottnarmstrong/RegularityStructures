/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductIPsiPsiCovField
public import Phi43.BPHZ.ProductIPsiPsiCovFour
public import Phi43.BPHZ.TreeWickSquare
public import Phi43.BPHZ.TreeI3PsiFieldFubini

/-!
# The covariance of `Π_x I(Ψ)Ψ` at two points

Write `T = ipsiTaylorKernel N x y`, `T' = ipsiTaylorKernel N x y'`, `Q = hairerCovariance N ρ ε`,
`p = proj y`, `p' = proj y'`.  Fubini for tested pairs (`integral_testedPair_eq`) and the
four-point formula give

`E[F(y) F(y')] = A A' + B Q(p - p') + R R'`

with `A = ∫ T(w) Q(w - p)`, `A' = ∫ T'(w) Q(w - p')`, `R = ∫ T(w) Q(w - p')`,
`R' = ∫ T'(w) Q(p - w)` and `B = E[v₁(x, y) v₁(x, y')]`
(`hairerIPsiPsiField_integral_mul`), provided the four integrands `T Q(· - ·)` are integrable.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ} {ξ : Ω → SpaceTime → ℝ}

/-- `E[v₁(x, y) v₁(x, y')] = ∫∫ T(w) T'(w') Q(w - w')`. -/
theorem hairerIPsiRecentred_integral_mul (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ) (x y y' : ParabolicSpace) :
    ∫ ω, hairerIPsiRecentred N ξ ω x y * hairerIPsiRecentred N ξ ω x y' ∂P =
      ∫ q : SpaceTime × SpaceTime, ipsiTaylorKernel N x y q.1 * ipsiTaylorKernel N x y' q.2 *
        hairerCovariance N ρ ε (q.1 - q.2) := by
  have := hW.isProbabilityMeasure
  have hY := measurable_hairerPsiField_uncurry N hξ
  have hi : ∀ q : SpaceTime × SpaceTime,
      Integrable (fun ω => hairerPsiField N ξ ω q.1 * (1 : ℝ) *
        (hairerPsiField N ξ ω q.2 * (1 : ℝ))) P := fun q => by
    simpa using (hairerPsiField_integral_abs_mul_two_le N hρ hε hW hξ q.1 q.2).1
  have hM : ∀ q : SpaceTime × SpaceTime,
      ∫ ω, |hairerPsiField N ξ ω q.1 * (1 : ℝ) * (hairerPsiField N ξ ω q.2 * (1 : ℝ))| ∂P ≤
        hairerCovariance N ρ ε 0 := fun q => by
    simpa using (hairerPsiField_integral_abs_mul_two_le N hρ hε hW hξ q.1 q.2).2
  have h := integral_testedPair_eq (P := P) (a := fun _ => (1 : ℝ)) (b := fun _ => (1 : ℝ)) hY hY
    measurable_const measurable_const (integrable_ipsiTaylorKernel N x y)
    (integrable_ipsiTaylorKernel N x y') hi hM
  have e1 : ∀ ω, hairerIPsiRecentred N ξ ω x y * hairerIPsiRecentred N ξ ω x y' =
      (∫ w, ipsiTaylorKernel N x y w * hairerPsiField N ξ ω w) * 1 *
        ((∫ w, ipsiTaylorKernel N x y' w * hairerPsiField N ξ ω w) * 1) := fun ω => by
    rw [hairerIPsiRecentred_eq_integral N (hξ.1 ω), hairerIPsiRecentred_eq_integral N (hξ.1 ω)]
    ring
  simp_rw [e1]
  rw [h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  simp only
  have := hairerPsiField_integral_mul N hρ hε hW hξ q.1 q.2
  have h2 : ∫ ω, hairerPsiField N ξ ω q.1 * (1 : ℝ) * (hairerPsiField N ξ ω q.2 * (1 : ℝ)) ∂P =
      hairerCovariance N ρ ε (q.1 - q.2) := by simpa using this
  rw [h2]

/-- **Covariance identity for `Π_x I(Ψ)Ψ`.** -/
theorem hairerIPsiPsiField_integral_mul (N : ℕ) (hρ : IsMollifier ρ) (hε : 0 < ε)
    (hW : IsWhiteNoise P W) (hξ : IsRegularisedNoise P W ρ ε ξ) (x y y' : ParabolicSpace)
    (hA : Integrable (fun w => ipsiTaylorKernel N x y w *
      hairerCovariance N ρ ε (w - spaceTimeProj y)))
    (hA' : Integrable (fun w => ipsiTaylorKernel N x y' w *
      hairerCovariance N ρ ε (w - spaceTimeProj y')))
    (hR : Integrable (fun w => ipsiTaylorKernel N x y w *
      hairerCovariance N ρ ε (w - spaceTimeProj y')))
    (hR' : Integrable (fun w => ipsiTaylorKernel N x y' w *
      hairerCovariance N ρ ε (spaceTimeProj y - w))) :
    ∫ ω, hairerIPsiPsiField N ξ x ω y * hairerIPsiPsiField N ξ x ω y' ∂P =
      (∫ w, ipsiTaylorKernel N x y w * hairerCovariance N ρ ε (w - spaceTimeProj y)) *
        (∫ w, ipsiTaylorKernel N x y' w * hairerCovariance N ρ ε (w - spaceTimeProj y')) +
      (∫ ω, hairerIPsiRecentred N ξ ω x y * hairerIPsiRecentred N ξ ω x y' ∂P) *
        hairerCovariance N ρ ε (spaceTimeProj y - spaceTimeProj y') +
      (∫ w, ipsiTaylorKernel N x y w * hairerCovariance N ρ ε (w - spaceTimeProj y')) *
        (∫ w, ipsiTaylorKernel N x y' w * hairerCovariance N ρ ε (spaceTimeProj y - w)) := by
  have := hW.isProbabilityMeasure
  set Q := hairerCovariance N ρ ε with hQ
  set p := spaceTimeProj y with hp
  set p' := spaceTimeProj y' with hp'
  have hY := measurable_hairerPsiField_uncurry N hξ
  have hfour := fun q : SpaceTime × SpaceTime =>
    hairerPsiField_integral_mul_four N hρ hε hW hξ q.1 p q.2 p'
  have hi : ∀ q : SpaceTime × SpaceTime,
      Integrable (fun ω => hairerPsiField N ξ ω q.1 * hairerPsiField N ξ ω p *
        (hairerPsiField N ξ ω q.2 * hairerPsiField N ξ ω p')) P := fun q => by
    refine (hfour q).1.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only; ring
  have hM : ∀ q : SpaceTime × SpaceTime,
      ∫ ω, |hairerPsiField N ξ ω q.1 * hairerPsiField N ξ ω p *
        (hairerPsiField N ξ ω q.2 * hairerPsiField N ξ ω p')| ∂P ≤ 3 * Q 0 ^ 2 := fun q => by
    have h := hairerPsiField_integral_abs_mul_four_le N hρ hε hW hξ q.1 p q.2 p'
    refine le_trans (le_of_eq (integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_))) h
    simp only; congr 1; ring
  have hmain := integral_testedPair_eq (P := P) (a := fun ω => hairerPsiField N ξ ω p)
    (b := fun ω => hairerPsiField N ξ ω p') hY hY (measurable_hairerPsiField_apply N hξ p)
    (measurable_hairerPsiField_apply N hξ p') (integrable_ipsiTaylorKernel N x y)
    (integrable_ipsiTaylorKernel N x y') hi hM
  have hexp := integrable_testedPair_expectation (P := P) (a := fun ω => hairerPsiField N ξ ω p)
    (b := fun ω => hairerPsiField N ξ ω p') hY hY (measurable_hairerPsiField_apply N hξ p)
    (measurable_hairerPsiField_apply N hξ p') (integrable_ipsiTaylorKernel N x y)
    (integrable_ipsiTaylorKernel N x y') hi hM
  have e1 : ∀ ω, hairerIPsiPsiField N ξ x ω y * hairerIPsiPsiField N ξ x ω y' =
      (∫ w, ipsiTaylorKernel N x y w * hairerPsiField N ξ ω w) * hairerPsiField N ξ ω p *
        ((∫ w, ipsiTaylorKernel N x y' w * hairerPsiField N ξ ω w) *
          hairerPsiField N ξ ω p') := fun ω => by
    unfold hairerIPsiPsiField
    rw [hairerIPsiRecentred_eq_integral N (hξ.1 ω), hairerIPsiRecentred_eq_integral N (hξ.1 ω)]
  simp_rw [e1]
  rw [hmain]
  have hpt : ∀ q : SpaceTime × SpaceTime,
      ipsiTaylorKernel N x y q.1 * ipsiTaylorKernel N x y' q.2 *
        ∫ ω, hairerPsiField N ξ ω q.1 * hairerPsiField N ξ ω p *
          (hairerPsiField N ξ ω q.2 * hairerPsiField N ξ ω p') ∂P =
      (ipsiTaylorKernel N x y q.1 * Q (q.1 - p)) * (ipsiTaylorKernel N x y' q.2 * Q (q.2 - p')) +
      ipsiTaylorKernel N x y q.1 * ipsiTaylorKernel N x y' q.2 * Q (q.1 - q.2) * Q (p - p') +
      (ipsiTaylorKernel N x y q.1 * Q (q.1 - p')) * (ipsiTaylorKernel N x y' q.2 * Q (p - q.2)) :=
    fun q => by
      have h4 := (hfour q).2
      have : ∫ ω, hairerPsiField N ξ ω q.1 * hairerPsiField N ξ ω p *
          (hairerPsiField N ξ ω q.2 * hairerPsiField N ξ ω p') ∂P =
          ∫ ω, hairerPsiField N ξ ω q.1 * hairerPsiField N ξ ω p * hairerPsiField N ξ ω q.2 *
            hairerPsiField N ξ ω p' ∂P :=
        integral_congr_ae (Filter.Eventually.of_forall fun ω => by simp only; ring)
      rw [this, h4]
      ring
  simp_rw [hpt]
  have i1 : Integrable (fun q : SpaceTime × SpaceTime =>
      (ipsiTaylorKernel N x y q.1 * Q (q.1 - p)) * (ipsiTaylorKernel N x y' q.2 * Q (q.2 - p'))) :=
    hA.mul_prod hA'
  have i3 : Integrable (fun q : SpaceTime × SpaceTime =>
      (ipsiTaylorKernel N x y q.1 * Q (q.1 - p')) * (ipsiTaylorKernel N x y' q.2 * Q (p - q.2))) :=
    hR.mul_prod hR'
  have iT : Integrable (fun q : SpaceTime × SpaceTime =>
      ipsiTaylorKernel N x y q.1 * ipsiTaylorKernel N x y' q.2 *
        ∫ ω, hairerPsiField N ξ ω q.1 * hairerPsiField N ξ ω p *
          (hairerPsiField N ξ ω q.2 * hairerPsiField N ξ ω p') ∂P) := hexp
  simp_rw [hpt] at iT
  have i2 : Integrable (fun q : SpaceTime × SpaceTime =>
      ipsiTaylorKernel N x y q.1 * ipsiTaylorKernel N x y' q.2 * Q (q.1 - q.2) * Q (p - p')) := by
    refine ((iT.sub i1).sub i3).congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [Pi.sub_apply]; ring
  have i12 : Integrable (fun q : SpaceTime × SpaceTime =>
      (ipsiTaylorKernel N x y q.1 * Q (q.1 - p)) * (ipsiTaylorKernel N x y' q.2 * Q (q.2 - p')) +
      ipsiTaylorKernel N x y q.1 * ipsiTaylorKernel N x y' q.2 * Q (q.1 - q.2) * Q (p - p')) :=
    i1.add i2
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
  rw [integral_add i12 i3, integral_add i1 i2, j1, j3, integral_mul_const,
    hairerIPsiRecentred_integral_mul N hρ hε hW hξ x y y']

end RegularityStructures.Phi43

end
