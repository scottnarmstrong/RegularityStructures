/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductIPsiPsiDiffDomination
public import Phi43.BPHZ.ProductIPsiPsiSqDiffSd
import Mathlib.Tactic

/-!
# Domination of the tested difference covariance for `I(Ψ)(Ψ² - c₁)`

For `Q = Q_t(x, ·)` and `h = ipsiWeightedKernel t x`, almost everywhere on `ℝ⁴ × ℝ⁴`,
`|Q(y) Q(y') Δe(y, y')| ≤ C m^(2θ) (...)` with a combination of `h h' Θ_{a,b} s(u - v)^(-ν)`
and `h h' s(u - v)^(-ν)` (`ipsiDiffSq_tested_dominated`).
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

theorem ipsiDiffSq_pointwise_alg {q q' c C M Wr Wr' E S3 D ud ra ra' ur ur' Dsq E3 TA TB T0 T02
    hh hh' a b b' : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hWr' : 0 ≤ Wr') (hE : 0 ≤ E) (hS3 : 0 ≤ S3) (hD : 0 ≤ D)
    (hra' : 0 ≤ ra') (hur' : 0 ≤ ur') (hud : 0 ≤ ud)
    (hh0 : 0 ≤ hh) (hh0' : 0 ≤ hh') (ha : 0 ≤ a) (hb : 0 ≤ b) (hbb : b ≤ b')
    (hc : |c| ≤ C * M * (((Wr * Wr' * E) * D) * S3 +
      (ra * ra' * (D * D)) * ((1 + ur) + (1 + ur') + (1 + ud))))
    (hES : E * D * S3 ≤ 4 * (TA + TB) + (T0 + T02)) (hDD : D * D = Dsq) (hDu : D * D * ud = E3)
    (hW : |q| * Wr ≤ a * hh) (hW' : |q'| * Wr' ≤ a * hh')
    (hV : |q| * (ra * (1 + ur)) ≤ 2 * b' * hh) (hV0 : |q| * ra ≤ b * hh)
    (hV' : |q'| * (ra' * (1 + ur')) ≤ 2 * b' * hh') (hV0' : |q'| * ra' ≤ b * hh') :
    |q * q' * c| ≤ C * M * ((a * a) * (4 * (hh * hh' * TA) + 4 * (hh * hh' * TB) +
      (hh * hh' * T0) + (hh * hh' * T02)) + (b * b') * (5 * (hh * hh' * Dsq)) +
      (b * b) * (hh * hh' * E3)) := by
  have hb' : 0 ≤ b' := hb.trans hbb
  have e : |q * q' * c| = |q| * |q'| * |c| := by rw [abs_mul, abs_mul]
  rw [e]
  have h1 : |q| * |q'| * |c| ≤ |q| * |q'| * (C * M * (((Wr * Wr' * E) * D) * S3 +
      (ra * ra' * (D * D)) * ((1 + ur) + (1 + ur') + (1 + ud)))) :=
    mul_le_mul_of_nonneg_left hc (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  refine h1.trans ?_
  have hWW : (|q| * Wr) * (|q'| * Wr') ≤ (a * hh) * (a * hh') :=
    mul_le_mul hW hW' (mul_nonneg (abs_nonneg _) hWr') (mul_nonneg ha hh0)
  have hES0 : 0 ≤ E * D * S3 := mul_nonneg (mul_nonneg hE hD) hS3
  have hXX : (|q| * Wr) * (|q'| * Wr') * (E * D * S3) ≤
      (a * hh) * (a * hh') * (4 * (TA + TB) + (T0 + T02)) :=
    mul_le_mul hWW hES hES0 (mul_nonneg (mul_nonneg ha hh0) (mul_nonneg ha hh0'))
  have P1 : (|q| * (ra * (1 + ur))) * (|q'| * ra') ≤ (2 * b' * hh) * (b * hh') :=
    mul_le_mul hV hV0' (mul_nonneg (abs_nonneg _) hra') (mul_nonneg (mul_nonneg (by norm_num) hb') hh0)
  have P2 : (|q| * ra) * (|q'| * (ra' * (1 + ur'))) ≤ (b * hh) * (2 * b' * hh') :=
    mul_le_mul hV0 hV' (mul_nonneg (abs_nonneg _) (mul_nonneg hra' (by linarith)))
      (mul_nonneg hb hh0)
  have P3 : (|q| * ra) * (|q'| * ra') * (1 + ud) ≤ (b * hh) * (b * hh') * (1 + ud) :=
    mul_le_mul_of_nonneg_right (mul_le_mul hV0 hV0' (mul_nonneg (abs_nonneg _) hra')
      (mul_nonneg hb hh0)) (by linarith)
  have hDD0 : 0 ≤ D * D := mul_nonneg hD hD
  have hsplit : |q| * |q'| * ((ra * ra' * (D * D)) * ((1 + ur) + (1 + ur') + (1 + ud))) =
      (D * D) * ((|q| * (ra * (1 + ur))) * (|q'| * ra') +
        (|q| * ra) * (|q'| * (ra' * (1 + ur'))) + (|q| * ra) * (|q'| * ra') * (1 + ud)) := by ring
  have hY : |q| * |q'| * ((ra * ra' * (D * D)) * ((1 + ur) + (1 + ur') + (1 + ud))) ≤
      (D * D) * ((2 * b' * hh) * (b * hh') + (b * hh) * (2 * b' * hh') +
        (b * hh) * (b * hh') * (1 + ud)) := by
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add P1 P2) P3) hDD0
  have hY2 : (D * D) * ((2 * b' * hh) * (b * hh') + (b * hh) * (2 * b' * hh') +
        (b * hh) * (b * hh') * (1 + ud)) =
      4 * (b * b') * (hh * hh' * Dsq) + (b * b) * (hh * hh' * Dsq) + (b * b) * (hh * hh' * E3) := by
    rw [← hDu, ← hDD]; ring
  have hbb2 : (b * b) * (hh * hh' * Dsq) ≤ (b * b') * (hh * hh' * Dsq) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbb hb)
      (mul_nonneg (mul_nonneg hh0 hh0') (hDD ▸ hDD0))
  have hXY : |q| * |q'| * (((Wr * Wr' * E) * D) * S3) ≤
      (a * a) * (4 * (hh * hh' * TA) + 4 * (hh * hh' * TB) + (hh * hh' * T0) +
        (hh * hh' * T02)) := by
    have : |q| * |q'| * (((Wr * Wr' * E) * D) * S3) =
        (|q| * Wr) * (|q'| * Wr') * (E * D * S3) := by ring
    rw [this]
    refine hXX.trans (le_of_eq ?_)
    ring
  have hCM : 0 ≤ C * M := mul_nonneg hC hM
  have hfin : |q| * |q'| * (((Wr * Wr' * E) * D) * S3 +
      (ra * ra' * (D * D)) * ((1 + ur) + (1 + ur') + (1 + ud))) ≤
      (a * a) * (4 * (hh * hh' * TA) + 4 * (hh * hh' * TB) + (hh * hh' * T0) +
        (hh * hh' * T02)) + (b * b') * (5 * (hh * hh' * Dsq)) + (b * b) * (hh * hh' * E3) := by
    rw [mul_add]
    have := add_le_add hXY (hY.trans (le_of_eq hY2))
    linarith [hbb2]
  calc |q| * |q'| * (C * M * (((Wr * Wr' * E) * D) * S3 +
        (ra * ra' * (D * D)) * ((1 + ur) + (1 + ur') + (1 + ud))))
      = C * M * (|q| * |q'| * (((Wr * Wr' * E) * D) * S3 +
        (ra * ra' * (D * D)) * ((1 + ur) + (1 + ur') + (1 + ud)))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hfin hCM


/-- **Almost everywhere domination of the tested difference covariance, Wick square.** -/
theorem ipsiDiffSq_tested_dominated (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ)
    (hρ' : IsMollifier ρ') {θ p γ δ : ℝ} (hθ : 0 < θ) (hθ4 : θ ≤ 1 / 4) (hp : 0 < p) (hp1 : p < 1)
    (hγ : 0 < γ) (hγ1 : γ < 1) (hγθ : γ + 2 * θ < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hθδ : 2 * θ + δ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
        ∀ᵐ q : ParabolicSpace × ParabolicSpace ∂volume,
          |parabolicSemigroup.kernel t x q.1 * parabolicSemigroup.kernel t x q.2 *
            arrSd (fun i j => ∫ ω, hairerIPsiPsiSqField N (![ξ, ξ'] i)
                (hairerWickConstant N (![ρ, ρ'] i) (![ε, ε'] i)) x ω q.1 *
              hairerIPsiPsiSqField N (![ξ, ξ'] j)
                (hairerWickConstant N (![ρ, ρ'] j) (![ε, ε'] j)) x ω q.2 ∂P)| ≤
          C * max ε ε' ^ (2 * θ) *
            (((t ^ (1 / 4 : ℝ)) ^ γ * (t ^ (1 / 4 : ℝ)) ^ γ) *
                (4 * (ipsiWeightedKernel t x q.1 * ipsiWeightedKernel t x q.2 *
                  (((1 + torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj x) ^ (-(p + 2 * θ))) *
                    (1 + torusParabolicSize (spaceTimeProj q.2 - spaceTimeProj x) ^ (-p))) *
                    torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj q.2) ^ (-(1 : ℝ)))) +
                 4 * (ipsiWeightedKernel t x q.1 * ipsiWeightedKernel t x q.2 *
                  (((1 + torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj x) ^ (-p)) *
                    (1 + torusParabolicSize (spaceTimeProj q.2 - spaceTimeProj x) ^
                      (-(p + 2 * θ)))) *
                    torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj q.2) ^ (-(1 : ℝ)))) +
                 (ipsiWeightedKernel t x q.1 * ipsiWeightedKernel t x q.2 *
                  (((1 + torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj x) ^ (-p)) *
                    (1 + torusParabolicSize (spaceTimeProj q.2 - spaceTimeProj x) ^ (-p))) *
                    torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj q.2) ^ (-(1 : ℝ)))) +
                 (ipsiWeightedKernel t x q.1 * ipsiWeightedKernel t x q.2 *
                  (((1 + torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj x) ^ (-p)) *
                    (1 + torusParabolicSize (spaceTimeProj q.2 - spaceTimeProj x) ^ (-p))) *
                    torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj q.2) ^ (-(1 + 2 * θ))))) +
              ((t ^ (1 / 4 : ℝ)) ^ ((3 - δ) / 2) * (t ^ (1 / 4 : ℝ)) ^ ((3 - δ) / 2 - 2 * θ)) *
                (5 * (ipsiWeightedKernel t x q.1 * ipsiWeightedKernel t x q.2 *
                  torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj q.2) ^ (-(2 : ℝ)))) +
              ((t ^ (1 / 4 : ℝ)) ^ ((3 - δ) / 2) * (t ^ (1 / 4 : ℝ)) ^ ((3 - δ) / 2)) *
                (ipsiWeightedKernel t x q.1 * ipsiWeightedKernel t x q.2 *
                  torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj q.2) ^
                    (-(2 + 2 * θ)))) := by
  obtain ⟨C, hC, hcov⟩ := ipsiMixSq_sd_abs_le.{u} N hρ hρ' hθ hθ4 hp hp1 hγ hγ1 hγθ hδ hδ1 hθδ
  refine ⟨C, hC, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' t ht ht1 x
  have hlam : 0 < t ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos ht _
  have hlam1 : t ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one ht.le ht1 (by norm_num)
  filter_upwards [ipsi_ae_time_ne x] with q ⟨h1, h2, h3⟩
  set y := q.1 with hy
  set y' := q.2 with hy'
  have p1 : 0 < torusParabolicSize (spaceTimeProj x - spaceTimeProj y) :=
    torusParabolicSize_pos_of_time_ne (z := spaceTimeProj x - spaceTimeProj y) (by
      simp only [spaceTimeProj, Prod.fst_sub]; exact sub_ne_zero.2 (Ne.symm h1))
  have p2 : 0 < torusParabolicSize (spaceTimeProj x - spaceTimeProj y') :=
    torusParabolicSize_pos_of_time_ne (z := spaceTimeProj x - spaceTimeProj y') (by
      simp only [spaceTimeProj, Prod.fst_sub]; exact sub_ne_zero.2 (Ne.symm h2))
  have p3 : 0 < torusParabolicSize (spaceTimeProj y - spaceTimeProj y') :=
    torusParabolicSize_pos_of_time_ne (z := spaceTimeProj y - spaceTimeProj y') (by
      simp only [spaceTimeProj, Prod.fst_sub]; exact sub_ne_zero.2 h3)
  have r1 : 0 < parabolicNorm (y - x) :=
    parabolicNorm_pos_of_time_ne (z := y - x) (by
      simp only [Prod.fst_sub]; exact sub_ne_zero.2 h1)
  have r2 : 0 < parabolicNorm (y' - x) :=
    parabolicNorm_pos_of_time_ne (z := y' - x) (by
      simp only [Prod.fst_sub]; exact sub_ne_zero.2 h2)
  have hc := hcov hW hε hε' hξ hξ' x y y' r1 r2 p1 p2 p3
  have sw1 := ipsi_size_swap (spaceTimeProj x) (spaceTimeProj y)
  have sw2 := ipsi_size_swap (spaceTimeProj x) (spaceTimeProj y')
  rw [sw1, sw2] at hc
  rw [sw1] at p1
  rw [sw2] at p2
  set l := t ^ (1 / 4 : ℝ) with hl
  set r := parabolicNorm (y - x) with hrdef
  set r' := parabolicNorm (y' - x) with hr'def
  set e1 := torusParabolicSize (spaceTimeProj y - spaceTimeProj x) with he1
  set e2 := torusParabolicSize (spaceTimeProj y' - spaceTimeProj x) with he2
  set d := torusParabolicSize (spaceTimeProj y - spaceTimeProj y') with hd
  have hα0 : 0 ≤ (3 - δ) / 2 - 2 * θ := by linarith
  have hα2 : (3 - δ) / 2 ≤ 2 := by linarith
  have hW1 := ipsi_weightW_le hlam hlam1 r1.le hγ.le hγ1.le
  have hW2 := ipsi_weightW_le hlam hlam1 r2.le hγ.le hγ1.le
  have hV1 := ipsi_rpow_le_weight (a := (3 - δ) / 2) hlam r1.le (by linarith) hα2
  have hV2 := ipsi_rpow_le_weight (a := (3 - δ) / 2) hlam r2.le (by linarith) hα2
  have hU1 := ipsi_rpow_le_weight (a := (3 - δ) / 2 - 2 * θ) hlam r1.le hα0 (by linarith)
  have hU2 := ipsi_rpow_le_weight (a := (3 - δ) / 2 - 2 * θ) hlam r2.le hα0 (by linarith)
  have hll : l ^ ((3 - δ) / 2) ≤ l ^ ((3 - δ) / 2 - 2 * θ) :=
    Real.rpow_le_rpow_of_exponent_ge hlam hlam1 (by linarith)
  have mk : ∀ (z : ParabolicSpace) {W' b : ℝ},
      W' ≤ b * (1 + parabolicNorm (z - x) / l) ^ 2 →
      |parabolicSemigroup.kernel t x z| * W' ≤ b * ipsiWeightedKernel t x z := by
    intro z W' b hh
    unfold ipsiWeightedKernel
    calc |parabolicSemigroup.kernel t x z| * W'
        ≤ |parabolicSemigroup.kernel t x z| * (b * (1 + parabolicNorm (z - x) / l) ^ 2) :=
          mul_le_mul_of_nonneg_left hh (abs_nonneg _)
      _ = _ := by ring
  have mk2 : ∀ {z : ParabolicSpace}, 0 < parabolicNorm (z - x) →
      parabolicNorm (z - x) ^ ((3 - δ) / 2) ≤ l ^ ((3 - δ) / 2) * (1 + parabolicNorm (z - x) / l) ^ 2 →
      parabolicNorm (z - x) ^ ((3 - δ) / 2 - 2 * θ) ≤
        l ^ ((3 - δ) / 2 - 2 * θ) * (1 + parabolicNorm (z - x) / l) ^ 2 →
      parabolicNorm (z - x) ^ ((3 - δ) / 2) * (1 + parabolicNorm (z - x) ^ (-(2 * θ))) ≤
        2 * l ^ ((3 - δ) / 2 - 2 * θ) * (1 + parabolicNorm (z - x) / l) ^ 2 := by
    intro z hz ha hb
    have e : parabolicNorm (z - x) ^ ((3 - δ) / 2) * (1 + parabolicNorm (z - x) ^ (-(2 * θ))) =
        parabolicNorm (z - x) ^ ((3 - δ) / 2) + parabolicNorm (z - x) ^ ((3 - δ) / 2 - 2 * θ) := by
      rw [mul_add, mul_one, ← Real.rpow_add hz, show (3 - δ) / 2 + -(2 * θ) = (3 - δ) / 2 - 2 * θ by ring]
    rw [e]
    have w0 : 0 ≤ (1 + parabolicNorm (z - x) / l) ^ 2 := sq_nonneg _
    have k := mul_le_mul_of_nonneg_right hll w0
    linarith only [ha, hb, k]
  have hla : 0 ≤ l ^ ((3 - δ) / 2) := Real.rpow_nonneg hlam.le _
  have hlg : 0 ≤ l ^ γ := Real.rpow_nonneg hlam.le _
  have hn1 := parabolicNorm_nonneg (y - x)
  have hn2 := parabolicNorm_nonneg (y' - x)
  have hE1 : 0 ≤ 1 + e1 ^ (-p) := by have := Real.rpow_nonneg p1.le (-p); linarith
  have hE2 : 0 ≤ 1 + e2 ^ (-p) := by have := Real.rpow_nonneg p2.le (-p); linarith
  have hS3 : 0 ≤ (1 + e1 ^ (-(2 * θ))) + (1 + e2 ^ (-(2 * θ))) + (1 + d ^ (-(2 * θ))) := by
    have a1 := Real.rpow_nonneg p1.le (-(2 * θ)); have a2 := Real.rpow_nonneg p2.le (-(2 * θ))
    have a3 := Real.rpow_nonneg p3.le (-(2 * θ))
    linarith
  have hD0 : 0 ≤ d ^ (-(1 : ℝ)) := Real.rpow_nonneg p3.le _
  have hDD : d ^ (-(1 : ℝ)) * d ^ (-(1 : ℝ)) = d ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_add p3]; norm_num
  have hDu : d ^ (-(1 : ℝ)) * d ^ (-(1 : ℝ)) * d ^ (-(2 * θ)) = d ^ (-(2 + 2 * θ)) := by
    rw [hDD, ← Real.rpow_add p3]; congr 1; ring
  have hD2 : d ^ (-(1 : ℝ)) * d ^ (-(2 * θ)) = d ^ (-(1 + 2 * θ)) := by
    rw [← Real.rpow_add p3]; congr 1; ring
  have hcomb := ipsi_theta_comb_le (t := 2 * θ) p1 p2 hp.le (by linarith)
  have hES : (1 + e1 ^ (-p)) * (1 + e2 ^ (-p)) * d ^ (-(1 : ℝ)) *
      ((1 + e1 ^ (-(2 * θ))) + (1 + e2 ^ (-(2 * θ))) + (1 + d ^ (-(2 * θ)))) ≤
      4 * (((1 + e1 ^ (-(p + 2 * θ))) * (1 + e2 ^ (-p))) * d ^ (-(1 : ℝ)) +
        ((1 + e1 ^ (-p)) * (1 + e2 ^ (-(p + 2 * θ)))) * d ^ (-(1 : ℝ))) +
      (((1 + e1 ^ (-p)) * (1 + e2 ^ (-p))) * d ^ (-(1 : ℝ)) +
        ((1 + e1 ^ (-p)) * (1 + e2 ^ (-p))) * d ^ (-(1 + 2 * θ))) := by
    have k := mul_le_mul_of_nonneg_left hcomb hD0
    rw [← hD2]
    nlinarith only [k]
  exact ipsiDiffSq_pointwise_alg (q := parabolicSemigroup.kernel t x y)
    (q' := parabolicSemigroup.kernel t x y') (hC := hC)
    (hM := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _)
    (hWr' := mul_nonneg (Real.rpow_nonneg hn2 _) (add_nonneg zero_le_one hn2))
    (hE := mul_nonneg hE1 hE2) (hS3 := hS3) (hD := hD0) (hra' := Real.rpow_nonneg hn2 _)
    (hur' := Real.rpow_nonneg hn2 _) (hud := Real.rpow_nonneg p3.le _)
    (hh0 := ipsiWeightedKernel_nonneg t x y) (hh0' := ipsiWeightedKernel_nonneg t x y')
    (ha := hlg) (hb := hla) (hbb := hll) (hc := hc) (hES := hES) (hDD := hDD) (hDu := hDu)
    (hW := mk y hW1) (hW' := mk y' hW2) (hV := mk y (mk2 r1 hV1 hU1)) (hV0 := mk y hV1)
    (hV' := mk y' (mk2 r2 hV2 hU2)) (hV0' := mk y' hV2)

end RegularityStructures.Phi43

end
