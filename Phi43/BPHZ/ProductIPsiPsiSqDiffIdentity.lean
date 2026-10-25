/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductIPsiPsiDiffIdentity
public import Phi43.BPHZ.ProductIPsiPsiSqDiffSix
public import Phi43.BPHZ.ProductIPsiPsiSqCovIdentity
import Mathlib.Tactic

/-!
# The covariance of `Π_x I(Ψ)(Ψ² - c₁)` for two models

With `F_i = hairerIPsiPsiSqField N (ξ i) c_i x` and the notation of `ProductIPsiPsiDiffIdentity`,
`E[F_i(y) F_j(y')] = 2 B_ij Q_ij(p - p')² + 4 A_i A'_j Q_ij(p - p') + 4 R_ij R'_ij Q_ij(p - p')`
(`hairerIPsiPsiSqField_mix_integral_mul`).
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
  {ρ : Fin 2 → ℝ × (Fin 3 → ℝ) → ℝ} {ε : Fin 2 → ℝ} {ξ : Fin 2 → Ω → SpaceTime → ℝ}

/-- **Covariance identity for `Π_x I(Ψ)(Ψ² - c₁)`, two models.** -/
theorem hairerIPsiPsiSqField_mix_integral_mul (N : ℕ) (hρ : ∀ i, IsMollifier (ρ i))
    (hε : ∀ i, 0 < ε i) (hW : IsWhiteNoise P W)
    (hξ : ∀ i, IsRegularisedNoise P W (ρ i) (ε i) (ξ i)) (i j : Fin 2) (x y y' : ParabolicSpace)
    (hA : Integrable (fun w => ipsiTaylorKernel N x y w *
      qMix N ρ ε i i (w - spaceTimeProj y)))
    (hA' : Integrable (fun w => ipsiTaylorKernel N x y' w *
      qMix N ρ ε j j (w - spaceTimeProj y')))
    (hR : Integrable (fun w => ipsiTaylorKernel N x y w *
      qMix N ρ ε i j (w - spaceTimeProj y')))
    (hR' : Integrable (fun w => ipsiTaylorKernel N x y' w *
      qMix N ρ ε i j (spaceTimeProj y - w))) :
    ∫ ω, hairerIPsiPsiSqField N (ξ i) (hairerWickConstant N (ρ i) (ε i)) x ω y *
        hairerIPsiPsiSqField N (ξ j) (hairerWickConstant N (ρ j) (ε j)) x ω y' ∂P =
      2 * (∫ ω, hairerIPsiRecentred N (ξ i) ω x y * hairerIPsiRecentred N (ξ j) ω x y' ∂P) *
          qMix N ρ ε i j (spaceTimeProj y - spaceTimeProj y') ^ 2 +
      4 * ((∫ w, ipsiTaylorKernel N x y w * qMix N ρ ε i i (w - spaceTimeProj y)) *
        (∫ w, ipsiTaylorKernel N x y' w * qMix N ρ ε j j (w - spaceTimeProj y')) *
          qMix N ρ ε i j (spaceTimeProj y - spaceTimeProj y')) +
      4 * ((∫ w, ipsiTaylorKernel N x y w * qMix N ρ ε i j (w - spaceTimeProj y')) *
        (∫ w, ipsiTaylorKernel N x y' w * qMix N ρ ε i j (spaceTimeProj y - w)) *
          qMix N ρ ε i j (spaceTimeProj y - spaceTimeProj y')) := by
  have := hW.isProbabilityMeasure
  set Q := qMix N ρ ε with hQ
  set p := spaceTimeProj y with hp
  set p' := spaceTimeProj y' with hp'
  have hwci : hairerWickConstant N (ρ i) (ε i) = hairerCovariance N (ρ i) (ε i) 0 :=
    hairerWickConstant_eq_covariance_zero N (ρ i) (ε i)
  have hwcj : hairerWickConstant N (ρ j) (ε j) = hairerCovariance N (ρ j) (ε j) 0 :=
    hairerWickConstant_eq_covariance_zero N (ρ j) (ε j)
  have hY := measurable_hairerPsiField_uncurry N (hξ i)
  have hY' := measurable_hairerPsiField_uncurry N (hξ j)
  have mS : ∀ (k : Fin 2) (z : SpaceTime), Measurable (fun ω => hairerPsiField N (ξ k) ω z ^ 2 -
      hairerCovariance N (ρ k) (ε k) 0) := fun k z =>
    ((measurable_hairerPsiField_apply N (hξ k) z).pow_const 2).sub_const _
  have hblock := fun q : SpaceTime × SpaceTime => psiMix_wick_block N hρ hε hW hξ i j q.1 p q.2 p'
  have hbabs := fun q : SpaceTime × SpaceTime => psiMix_wick_block_abs_le N hρ hε hW hξ i j q.1 p q.2 p'
  have hi : ∀ q : SpaceTime × SpaceTime,
      Integrable (fun ω => hairerPsiField N (ξ i) ω q.1 *
        (hairerPsiField N (ξ i) ω p ^ 2 - hairerCovariance N (ρ i) (ε i) 0) *
        (hairerPsiField N (ξ j) ω q.2 *
          (hairerPsiField N (ξ j) ω p' ^ 2 - hairerCovariance N (ρ j) (ε j) 0))) P := fun q => by
    refine (hblock q).1.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only; ring
  have hM : ∀ q : SpaceTime × SpaceTime,
      ∫ ω, |hairerPsiField N (ξ i) ω q.1 *
        (hairerPsiField N (ξ i) ω p ^ 2 - hairerCovariance N (ρ i) (ε i) 0) *
        (hairerPsiField N (ξ j) ω q.2 *
          (hairerPsiField N (ξ j) ω p' ^ 2 - hairerCovariance N (ρ j) (ε j) 0))| ∂P ≤
      (3 * hairerCovariance N (ρ i) (ε i) 0 ^ 2 + 60 * hairerCovariance N (ρ i) (ε i) 0 ^ 4 +
        3 * hairerCovariance N (ρ j) (ε j) 0 ^ 2 + 60 * hairerCovariance N (ρ j) (ε j) 0 ^ 4) / 4 :=
    fun q => by
    refine le_trans (le_of_eq (integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)))
      (hbabs q)
    simp only; congr 1; ring
  have hmain := integral_testedPair_eq (P := P)
    (a := fun ω => hairerPsiField N (ξ i) ω p ^ 2 - hairerCovariance N (ρ i) (ε i) 0)
    (b := fun ω => hairerPsiField N (ξ j) ω p' ^ 2 - hairerCovariance N (ρ j) (ε j) 0)
    hY hY' (mS i p) (mS j p')
    (integrable_ipsiTaylorKernel N x y) (integrable_ipsiTaylorKernel N x y') hi hM
  have hexp := integrable_testedPair_expectation (P := P)
    (a := fun ω => hairerPsiField N (ξ i) ω p ^ 2 - hairerCovariance N (ρ i) (ε i) 0)
    (b := fun ω => hairerPsiField N (ξ j) ω p' ^ 2 - hairerCovariance N (ρ j) (ε j) 0)
    hY hY' (mS i p) (mS j p')
    (integrable_ipsiTaylorKernel N x y) (integrable_ipsiTaylorKernel N x y') hi hM
  have e1 : ∀ ω, hairerIPsiPsiSqField N (ξ i) (hairerWickConstant N (ρ i) (ε i)) x ω y *
      hairerIPsiPsiSqField N (ξ j) (hairerWickConstant N (ρ j) (ε j)) x ω y' =
      (∫ w, ipsiTaylorKernel N x y w * hairerPsiField N (ξ i) ω w) *
        (hairerPsiField N (ξ i) ω p ^ 2 - hairerCovariance N (ρ i) (ε i) 0) *
        ((∫ w, ipsiTaylorKernel N x y' w * hairerPsiField N (ξ j) ω w) *
          (hairerPsiField N (ξ j) ω p' ^ 2 - hairerCovariance N (ρ j) (ε j) 0)) := fun ω => by
    unfold hairerIPsiPsiSqField hairerTreePsiSq
    rw [hairerIPsiRecentred_eq_integral N ((hξ i).1 ω), hairerIPsiRecentred_eq_integral N ((hξ j).1 ω),
      hwci, hwcj]
  simp_rw [e1]
  rw [hmain]
  have hpt : ∀ q : SpaceTime × SpaceTime,
      ipsiTaylorKernel N x y q.1 * ipsiTaylorKernel N x y' q.2 *
        ∫ ω, hairerPsiField N (ξ i) ω q.1 *
          (hairerPsiField N (ξ i) ω p ^ 2 - hairerCovariance N (ρ i) (ε i) 0) *
          (hairerPsiField N (ξ j) ω q.2 *
            (hairerPsiField N (ξ j) ω p' ^ 2 - hairerCovariance N (ρ j) (ε j) 0)) ∂P =
      4 * Q i j (p - p') * ((ipsiTaylorKernel N x y q.1 * Q i i (q.1 - p)) *
        (ipsiTaylorKernel N x y' q.2 * Q j j (q.2 - p'))) +
      2 * Q i j (p - p') ^ 2 * (ipsiTaylorKernel N x y q.1 * ipsiTaylorKernel N x y' q.2 *
        Q i j (q.1 - q.2)) +
      4 * Q i j (p - p') * ((ipsiTaylorKernel N x y q.1 * Q i j (q.1 - p')) *
        (ipsiTaylorKernel N x y' q.2 * Q i j (p - q.2))) := fun q => by
    have h4 := (hblock q).2
    have : ∫ ω, hairerPsiField N (ξ i) ω q.1 *
        (hairerPsiField N (ξ i) ω p ^ 2 - hairerCovariance N (ρ i) (ε i) 0) *
        (hairerPsiField N (ξ j) ω q.2 *
          (hairerPsiField N (ξ j) ω p' ^ 2 - hairerCovariance N (ρ j) (ε j) 0)) ∂P =
        ∫ ω, hairerPsiField N (ξ i) ω q.1 *
          (hairerPsiField N (ξ i) ω p ^ 2 - hairerCovariance N (ρ i) (ε i) 0) *
          hairerPsiField N (ξ j) ω q.2 *
          (hairerPsiField N (ξ j) ω p' ^ 2 - hairerCovariance N (ρ j) (ε j) 0) ∂P :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => by simp only; ring)
    rw [this, h4]
    ring
  simp_rw [hpt]
  have i1 : Integrable (fun q : SpaceTime × SpaceTime =>
      4 * Q i j (p - p') * ((ipsiTaylorKernel N x y q.1 * Q i i (q.1 - p)) *
        (ipsiTaylorKernel N x y' q.2 * Q j j (q.2 - p')))) := (hA.mul_prod hA').const_mul _
  have i3 : Integrable (fun q : SpaceTime × SpaceTime =>
      4 * Q i j (p - p') * ((ipsiTaylorKernel N x y q.1 * Q i j (q.1 - p')) *
        (ipsiTaylorKernel N x y' q.2 * Q i j (p - q.2)))) := (hR.mul_prod hR').const_mul _
  have iT : Integrable (fun q : SpaceTime × SpaceTime =>
      ipsiTaylorKernel N x y q.1 * ipsiTaylorKernel N x y' q.2 *
        ∫ ω, hairerPsiField N (ξ i) ω q.1 *
          (hairerPsiField N (ξ i) ω p ^ 2 - hairerCovariance N (ρ i) (ε i) 0) *
          (hairerPsiField N (ξ j) ω q.2 *
            (hairerPsiField N (ξ j) ω p' ^ 2 - hairerCovariance N (ρ j) (ε j) 0)) ∂P) := hexp
  simp_rw [hpt] at iT
  have i2 : Integrable (fun q : SpaceTime × SpaceTime =>
      2 * Q i j (p - p') ^ 2 * (ipsiTaylorKernel N x y q.1 * ipsiTaylorKernel N x y' q.2 *
        Q i j (q.1 - q.2))) := by
    refine ((iT.sub i1).sub i3).congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [Pi.sub_apply]; ring
  have i12 : Integrable (fun q : SpaceTime × SpaceTime =>
      4 * Q i j (p - p') * ((ipsiTaylorKernel N x y q.1 * Q i i (q.1 - p)) *
        (ipsiTaylorKernel N x y' q.2 * Q j j (q.2 - p'))) +
      2 * Q i j (p - p') ^ 2 * (ipsiTaylorKernel N x y q.1 * ipsiTaylorKernel N x y' q.2 *
        Q i j (q.1 - q.2))) := i1.add i2
  have j1 : ∫ q : SpaceTime × SpaceTime, (ipsiTaylorKernel N x y q.1 * Q i i (q.1 - p)) *
      (ipsiTaylorKernel N x y' q.2 * Q j j (q.2 - p')) =
      (∫ w, ipsiTaylorKernel N x y w * Q i i (w - p)) *
        ∫ w, ipsiTaylorKernel N x y' w * Q j j (w - p') :=
    integral_prod_mul (μ := (volume : Measure SpaceTime)) (ν := volume)
      (fun w => ipsiTaylorKernel N x y w * Q i i (w - p))
      (fun w => ipsiTaylorKernel N x y' w * Q j j (w - p'))
  have j3 : ∫ q : SpaceTime × SpaceTime, (ipsiTaylorKernel N x y q.1 * Q i j (q.1 - p')) *
      (ipsiTaylorKernel N x y' q.2 * Q i j (p - q.2)) =
      (∫ w, ipsiTaylorKernel N x y w * Q i j (w - p')) *
        ∫ w, ipsiTaylorKernel N x y' w * Q i j (p - w) :=
    integral_prod_mul (μ := (volume : Measure SpaceTime)) (ν := volume)
      (fun w => ipsiTaylorKernel N x y w * Q i j (w - p'))
      (fun w => ipsiTaylorKernel N x y' w * Q i j (p - w))
  rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
    integral_const_mul, j1, j3, hairerIPsiRecentred_mix_integral_mul N hρ hε hW hξ i j x y y']
  ring

end RegularityStructures.Phi43

end
