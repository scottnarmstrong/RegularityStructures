/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductIPsiPsiDiffFour
public import Phi43.BPHZ.ProductIPsiPsiCovIdentity
import Mathlib.Tactic

/-!
# The covariance of `Π_x I(Ψ)Ψ` for two models

With `F_i = hairerIPsiPsiField N (ξ i) x`, `T = ipsiTaylorKernel`, `p = proj y`, `p' = proj y'`,
`E[F_i(y) F_j(y')] = A_i A'_j + B_{ij} Q_{ij}(p - p') + R_{ij} R'_{ij}`, where
`A_i = ∫ T Q_ii(· - p)`, `A'_j = ∫ T' Q_jj(· - p')`, `R_ij = ∫ T Q_ij(· - p')`,
`R'_ij = ∫ T' Q_ij(p - ·)` and `B_ij = E[v_i(y) v_j(y')]`
(`hairerIPsiPsiField_mix_integral_mul`).
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
  {ρ : Fin 2 → ℝ × (Fin 3 → ℝ) → ℝ} {ε : Fin 2 → ℝ} {ξ : Fin 2 → Ω → SpaceTime → ℝ}

/-- `E[v_i(x, y) v_j(x, y')] = ∫∫ T T' Q_ij(w - w')`. -/
theorem hairerIPsiRecentred_mix_integral_mul (N : ℕ) (hρ : ∀ i, IsMollifier (ρ i))
    (hε : ∀ i, 0 < ε i) (hW : IsWhiteNoise P W)
    (hξ : ∀ i, IsRegularisedNoise P W (ρ i) (ε i) (ξ i)) (i j : Fin 2) (x y y' : ParabolicSpace) :
    ∫ ω, hairerIPsiRecentred N (ξ i) ω x y * hairerIPsiRecentred N (ξ j) ω x y' ∂P =
      ∫ q : SpaceTime × SpaceTime, ipsiTaylorKernel N x y q.1 * ipsiTaylorKernel N x y' q.2 *
        qMix N ρ ε i j (q.1 - q.2) := by
  have := hW.isProbabilityMeasure
  have hY := measurable_hairerPsiField_uncurry N (hξ i)
  have hY' := measurable_hairerPsiField_uncurry N (hξ j)
  have h2 : ∀ a b : SpaceTime,
      Integrable (fun ω => hairerPsiField N (ξ i) ω a * hairerPsiField N (ξ j) ω b) P ∧
      ∫ ω, |hairerPsiField N (ξ i) ω a * hairerPsiField N (ξ j) ω b| ∂P ≤
        (hairerCovariance N (ρ i) (ε i) 0 + hairerCovariance N (ρ j) (ε j) 0) / 2 := by
    intro a b
    have mi := (hairerPsiField_memLp N (hρ i) (hε i) hW (hξ i) a)
    have mj := (hairerPsiField_memLp N (hρ j) (hε j) hW (hξ j) b)
    have hm : Integrable (fun ω => hairerPsiField N (ξ i) ω a * hairerPsiField N (ξ j) ω b) P :=
      mi.integrable_mul mj
    have hsa : Integrable (fun ω => hairerPsiField N (ξ i) ω a * hairerPsiField N (ξ i) ω a) P :=
      mi.integrable_mul mi
    have hsb : Integrable (fun ω => hairerPsiField N (ξ j) ω b * hairerPsiField N (ξ j) ω b) P :=
      mj.integrable_mul mj
    refine ⟨hm, ?_⟩
    calc ∫ ω, |hairerPsiField N (ξ i) ω a * hairerPsiField N (ξ j) ω b| ∂P
        ≤ ∫ ω, (hairerPsiField N (ξ i) ω a * hairerPsiField N (ξ i) ω a +
            hairerPsiField N (ξ j) ω b * hairerPsiField N (ξ j) ω b) / 2 ∂P := by
          refine integral_mono hm.abs ((hsa.add hsb).div_const 2) fun ω => ?_
          rw [abs_le]; constructor <;>
            nlinarith [sq_nonneg (hairerPsiField N (ξ i) ω a + hairerPsiField N (ξ j) ω b),
              sq_nonneg (hairerPsiField N (ξ i) ω a - hairerPsiField N (ξ j) ω b)]
      _ = _ := by
          rw [integral_div, integral_add hsa hsb, hairerPsiField_integral_mul N (hρ i) (hε i) hW
            (hξ i), hairerPsiField_integral_mul N (hρ j) (hε j) hW (hξ j)]
          simp
  have hi : ∀ q : SpaceTime × SpaceTime,
      Integrable (fun ω => hairerPsiField N (ξ i) ω q.1 * (1 : ℝ) *
        (hairerPsiField N (ξ j) ω q.2 * (1 : ℝ))) P := fun q => by
    simpa using (h2 q.1 q.2).1
  have hM : ∀ q : SpaceTime × SpaceTime,
      ∫ ω, |hairerPsiField N (ξ i) ω q.1 * (1 : ℝ) * (hairerPsiField N (ξ j) ω q.2 * (1 : ℝ))| ∂P ≤
        (hairerCovariance N (ρ i) (ε i) 0 + hairerCovariance N (ρ j) (ε j) 0) / 2 := fun q => by
    simpa using (h2 q.1 q.2).2
  have h := integral_testedPair_eq (P := P) (a := fun _ => (1 : ℝ)) (b := fun _ => (1 : ℝ)) hY hY'
    measurable_const measurable_const (integrable_ipsiTaylorKernel N x y)
    (integrable_ipsiTaylorKernel N x y') hi hM
  have e1 : ∀ ω, hairerIPsiRecentred N (ξ i) ω x y * hairerIPsiRecentred N (ξ j) ω x y' =
      (∫ w, ipsiTaylorKernel N x y w * hairerPsiField N (ξ i) ω w) * 1 *
        ((∫ w, ipsiTaylorKernel N x y' w * hairerPsiField N (ξ j) ω w) * 1) := fun ω => by
    rw [hairerIPsiRecentred_eq_integral N ((hξ i).1 ω),
      hairerIPsiRecentred_eq_integral N ((hξ j).1 ω)]
    ring
  simp_rw [e1]
  rw [h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  simp only
  have := (psiMix_integral_mul_two N hρ hε hW hξ i j q.1 q.2)
  have h2' : ∫ ω, hairerPsiField N (ξ i) ω q.1 * (1 : ℝ) * (hairerPsiField N (ξ j) ω q.2 * (1 : ℝ)) ∂P =
      qMix N ρ ε i j (q.1 - q.2) := by simpa using this
  rw [h2']

/-- **Covariance identity for `Π_x I(Ψ)Ψ`, two models.** -/
theorem hairerIPsiPsiField_mix_integral_mul (N : ℕ) (hρ : ∀ i, IsMollifier (ρ i))
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
    ∫ ω, hairerIPsiPsiField N (ξ i) x ω y * hairerIPsiPsiField N (ξ j) x ω y' ∂P =
      (∫ w, ipsiTaylorKernel N x y w * qMix N ρ ε i i (w - spaceTimeProj y)) *
        (∫ w, ipsiTaylorKernel N x y' w * qMix N ρ ε j j (w - spaceTimeProj y')) +
      (∫ ω, hairerIPsiRecentred N (ξ i) ω x y * hairerIPsiRecentred N (ξ j) ω x y' ∂P) *
        qMix N ρ ε i j (spaceTimeProj y - spaceTimeProj y') +
      (∫ w, ipsiTaylorKernel N x y w * qMix N ρ ε i j (w - spaceTimeProj y')) *
        (∫ w, ipsiTaylorKernel N x y' w * qMix N ρ ε i j (spaceTimeProj y - w)) := by
  have := hW.isProbabilityMeasure
  set Q := qMix N ρ ε with hQ
  set p := spaceTimeProj y with hp
  set p' := spaceTimeProj y' with hp'
  have hY := measurable_hairerPsiField_uncurry N (hξ i)
  have hY' := measurable_hairerPsiField_uncurry N (hξ j)
  have hfour := fun q : SpaceTime × SpaceTime =>
    psiMix_integral_mul_four N hρ hε hW hξ ![i, i, j, j] ![q.1, p, q.2, p']
  have hbd := fun q : SpaceTime × SpaceTime =>
    psiMix_abs_mul_four_le N hρ hε hW hξ ![i, i, j, j] ![q.1, p, q.2, p']
  have hi : ∀ q : SpaceTime × SpaceTime,
      Integrable (fun ω => hairerPsiField N (ξ i) ω q.1 * hairerPsiField N (ξ i) ω p *
        (hairerPsiField N (ξ j) ω q.2 * hairerPsiField N (ξ j) ω p')) P := fun q => by
    refine (hfour q).1.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]; ring
  have hM : ∀ q : SpaceTime × SpaceTime,
      ∫ ω, |hairerPsiField N (ξ i) ω q.1 * hairerPsiField N (ξ i) ω p *
        (hairerPsiField N (ξ j) ω q.2 * hairerPsiField N (ξ j) ω p')| ∂P ≤
      (3 * hairerCovariance N (ρ i) (ε i) 0 ^ 2 + 3 * hairerCovariance N (ρ i) (ε i) 0 ^ 2 +
        3 * hairerCovariance N (ρ j) (ε j) 0 ^ 2 + 3 * hairerCovariance N (ρ j) (ε j) 0 ^ 2) / 4 :=
    fun q => by
    have h := hbd q
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at h
    refine le_trans (le_of_eq (integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_))) h
    simp only; congr 1; ring
  have hmain := integral_testedPair_eq (P := P) (a := fun ω => hairerPsiField N (ξ i) ω p)
    (b := fun ω => hairerPsiField N (ξ j) ω p') hY hY'
    (measurable_hairerPsiField_apply N (hξ i) p) (measurable_hairerPsiField_apply N (hξ j) p')
    (integrable_ipsiTaylorKernel N x y) (integrable_ipsiTaylorKernel N x y') hi hM
  have hexp := integrable_testedPair_expectation (P := P)
    (a := fun ω => hairerPsiField N (ξ i) ω p) (b := fun ω => hairerPsiField N (ξ j) ω p') hY hY'
    (measurable_hairerPsiField_apply N (hξ i) p) (measurable_hairerPsiField_apply N (hξ j) p')
    (integrable_ipsiTaylorKernel N x y) (integrable_ipsiTaylorKernel N x y') hi hM
  have e1 : ∀ ω, hairerIPsiPsiField N (ξ i) x ω y * hairerIPsiPsiField N (ξ j) x ω y' =
      (∫ w, ipsiTaylorKernel N x y w * hairerPsiField N (ξ i) ω w) *
        hairerPsiField N (ξ i) ω p *
        ((∫ w, ipsiTaylorKernel N x y' w * hairerPsiField N (ξ j) ω w) *
          hairerPsiField N (ξ j) ω p') := fun ω => by
    unfold hairerIPsiPsiField
    rw [hairerIPsiRecentred_eq_integral N ((hξ i).1 ω),
      hairerIPsiRecentred_eq_integral N ((hξ j).1 ω)]
  simp_rw [e1]
  rw [hmain]
  have hpt : ∀ q : SpaceTime × SpaceTime,
      ipsiTaylorKernel N x y q.1 * ipsiTaylorKernel N x y' q.2 *
        ∫ ω, hairerPsiField N (ξ i) ω q.1 * hairerPsiField N (ξ i) ω p *
          (hairerPsiField N (ξ j) ω q.2 * hairerPsiField N (ξ j) ω p') ∂P =
      (ipsiTaylorKernel N x y q.1 * Q i i (q.1 - p)) *
        (ipsiTaylorKernel N x y' q.2 * Q j j (q.2 - p')) +
      ipsiTaylorKernel N x y q.1 * ipsiTaylorKernel N x y' q.2 * Q i j (q.1 - q.2) *
        Q i j (p - p') +
      (ipsiTaylorKernel N x y q.1 * Q i j (q.1 - p')) *
        (ipsiTaylorKernel N x y' q.2 * Q i j (p - q.2)) := fun q => by
    have h4 := (hfour q).2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at h4
    have : ∫ ω, hairerPsiField N (ξ i) ω q.1 * hairerPsiField N (ξ i) ω p *
        (hairerPsiField N (ξ j) ω q.2 * hairerPsiField N (ξ j) ω p') ∂P =
        ∫ ω, hairerPsiField N (ξ i) ω q.1 * hairerPsiField N (ξ i) ω p *
          hairerPsiField N (ξ j) ω q.2 * hairerPsiField N (ξ j) ω p' ∂P :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => by simp only; ring)
    rw [this, h4]
    ring
  simp_rw [hpt]
  have i1 : Integrable (fun q : SpaceTime × SpaceTime =>
      (ipsiTaylorKernel N x y q.1 * Q i i (q.1 - p)) *
        (ipsiTaylorKernel N x y' q.2 * Q j j (q.2 - p'))) := hA.mul_prod hA'
  have i3 : Integrable (fun q : SpaceTime × SpaceTime =>
      (ipsiTaylorKernel N x y q.1 * Q i j (q.1 - p')) *
        (ipsiTaylorKernel N x y' q.2 * Q i j (p - q.2))) := hR.mul_prod hR'
  have iT : Integrable (fun q : SpaceTime × SpaceTime =>
      ipsiTaylorKernel N x y q.1 * ipsiTaylorKernel N x y' q.2 *
        ∫ ω, hairerPsiField N (ξ i) ω q.1 * hairerPsiField N (ξ i) ω p *
          (hairerPsiField N (ξ j) ω q.2 * hairerPsiField N (ξ j) ω p') ∂P) := hexp
  simp_rw [hpt] at iT
  have i2 : Integrable (fun q : SpaceTime × SpaceTime =>
      ipsiTaylorKernel N x y q.1 * ipsiTaylorKernel N x y' q.2 * Q i j (q.1 - q.2) *
        Q i j (p - p')) := by
    refine ((iT.sub i1).sub i3).congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [Pi.sub_apply]; ring
  have i12 : Integrable (fun q : SpaceTime × SpaceTime =>
      (ipsiTaylorKernel N x y q.1 * Q i i (q.1 - p)) *
        (ipsiTaylorKernel N x y' q.2 * Q j j (q.2 - p')) +
      ipsiTaylorKernel N x y q.1 * ipsiTaylorKernel N x y' q.2 * Q i j (q.1 - q.2) *
        Q i j (p - p')) := i1.add i2
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
  rw [integral_add i12 i3, integral_add i1 i2, j1, j3, integral_mul_const,
    hairerIPsiRecentred_mix_integral_mul N hρ hε hW hξ i j x y y']

end RegularityStructures.Phi43

end
