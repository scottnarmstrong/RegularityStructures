/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductIPsiPsiSecondDomination
public import Phi43.BPHZ.ProductIPsiPsiDiffSd
import Mathlib.Tactic

/-!
# Domination of the tested difference covariance by a periodisable majorant

For `Q = Q_t(x, ·)` and `h = ipsiWeightedKernel t x`, almost everywhere on `ℝ⁴ × ℝ⁴`,
`|Q(y) Q(y') Δe(y, y')| ≤ C m^(2θ) (...)`, where `(...)` is a combination of
`h h' Θ_{p+2θ, p}`, `h h' Θ_{p, p+2θ}`, `h h' s(u - v)^(-1)` and `h h' s(u - v)^(-(1+2θ))`
with the powers `lam^(2γ)`, `lam^(2α - 2θ)`, `lam^(2α)` (`ipsiDiff_tested_dominated`).
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

theorem ipsi_theta_prod_le {e a b : ℝ} (he : 0 < e) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (1 + e ^ (-a)) * (1 + e ^ (-b)) ≤ 4 * (1 + e ^ (-(a + b))) := by
  have hZ : e ^ (-(a + b)) = e ^ (-a) * e ^ (-b) := by
    rw [← Real.rpow_add he]; congr 1; ring
  rw [hZ]
  have hX := Real.rpow_nonneg he.le (-a)
  have hY := Real.rpow_nonneg he.le (-b)
  rcases le_or_gt 1 e with h1 | h1
  · have X1 : e ^ (-a) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
    have Y1 : e ^ (-b) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
    nlinarith [mul_nonneg hX hY]
  · have X1 : 1 ≤ e ^ (-a) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos he h1.le (by linarith)
    have Y1 : 1 ≤ e ^ (-b) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos he h1.le (by linarith)
    nlinarith [mul_nonneg (sub_nonneg.2 X1) (sub_nonneg.2 Y1)]

/-- The combination `E (S₁)` of the two `e`-factors, as the two-exponent weights. -/
theorem ipsi_theta_comb_le {e1 e2 p t : ℝ} (h1 : 0 < e1) (h2 : 0 < e2) (hp : 0 ≤ p) (ht : 0 ≤ t) :
    ((1 + e1 ^ (-p)) * (1 + e2 ^ (-p))) * ((1 + e1 ^ (-t)) + (1 + e2 ^ (-t))) ≤
      4 * ((1 + e1 ^ (-(p + t))) * (1 + e2 ^ (-p)) +
        (1 + e1 ^ (-p)) * (1 + e2 ^ (-(p + t)))) := by
  have a1 := ipsi_theta_prod_le h1 hp ht
  have a2 := ipsi_theta_prod_le h2 hp ht
  have n1 : 0 ≤ 1 + e1 ^ (-p) := by have := Real.rpow_nonneg h1.le (-p); linarith
  have n2 : 0 ≤ 1 + e2 ^ (-p) := by have := Real.rpow_nonneg h2.le (-p); linarith
  have k1 := mul_le_mul_of_nonneg_right a1 n2
  have k2 := mul_le_mul_of_nonneg_left a2 n1
  nlinarith [k1, k2]

theorem ipsiDiff_pointwise_alg {q q' c C M Wr Wr' E S1 ra ra' ur ur' ud D D2 TA TB hh hh' a b b' : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hWr' : 0 ≤ Wr') (hE : 0 ≤ E) (hS1 : 0 ≤ S1)
    (hra' : 0 ≤ ra') (hur' : 0 ≤ ur') (hud : 0 ≤ ud) (hD : 0 ≤ D)
    (hh0 : 0 ≤ hh) (hh0' : 0 ≤ hh') (ha : 0 ≤ a) (hb : 0 ≤ b) (hbb : b ≤ b')
    (hc : |c| ≤ C * M * ((Wr * Wr' * E) * S1 + (ra * ra' * D) * ((1 + ur) + (1 + ur') + (1 + ud))))
    (hES : E * S1 ≤ 4 * (TA + TB)) (hD2 : D * ud = D2)
    (hW : |q| * Wr ≤ a * hh) (hW' : |q'| * Wr' ≤ a * hh')
    (hV : |q| * (ra * (1 + ur)) ≤ 2 * b' * hh) (hV0 : |q| * ra ≤ b * hh)
    (hV' : |q'| * (ra' * (1 + ur')) ≤ 2 * b' * hh') (hV0' : |q'| * ra' ≤ b * hh') :
    |q * q' * c| ≤ C * M * ((a * a) * (4 * (hh * hh' * TA) + 4 * (hh * hh' * TB)) +
      (b * b') * (5 * (hh * hh' * D)) + (b * b) * (hh * hh' * D2)) := by
  have hb' : 0 ≤ b' := hb.trans hbb
  have e : |q * q' * c| = |q| * |q'| * |c| := by rw [abs_mul, abs_mul]
  rw [e]
  have h1 : |q| * |q'| * |c| ≤ |q| * |q'| * (C * M * ((Wr * Wr' * E) * S1 +
      (ra * ra' * D) * ((1 + ur) + (1 + ur') + (1 + ud)))) :=
    mul_le_mul_of_nonneg_left hc (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  refine h1.trans ?_
  -- the X part
  have hWW : (|q| * Wr) * (|q'| * Wr') ≤ (a * hh) * (a * hh') :=
    mul_le_mul hW hW' (mul_nonneg (abs_nonneg _) hWr') (mul_nonneg ha hh0)
  have hES0 : 0 ≤ E * S1 := mul_nonneg hE hS1
  have hXX : (|q| * Wr) * (|q'| * Wr') * (E * S1) ≤ (a * hh) * (a * hh') * (4 * (TA + TB)) :=
    mul_le_mul hWW hES hES0 (mul_nonneg (mul_nonneg ha hh0) (mul_nonneg ha hh0'))
  -- the Y part
  have P1 : (|q| * (ra * (1 + ur))) * (|q'| * ra') ≤ (2 * b' * hh) * (b * hh') :=
    mul_le_mul hV hV0' (mul_nonneg (abs_nonneg _) hra') (mul_nonneg (mul_nonneg (by norm_num) hb') hh0)
  have P2 : (|q| * ra) * (|q'| * (ra' * (1 + ur'))) ≤ (b * hh) * (2 * b' * hh') :=
    mul_le_mul hV0 hV' (mul_nonneg (abs_nonneg _) (mul_nonneg hra' (by linarith)))
      (mul_nonneg hb hh0)
  have P3 : (|q| * ra) * (|q'| * ra') * (1 + ud) ≤ (b * hh) * (b * hh') * (1 + ud) :=
    mul_le_mul_of_nonneg_right (mul_le_mul hV0 hV0' (mul_nonneg (abs_nonneg _) hra')
      (mul_nonneg hb hh0)) (by linarith)
  have hsplit : |q| * |q'| * ((ra * ra' * D) * ((1 + ur) + (1 + ur') + (1 + ud))) =
      D * ((|q| * (ra * (1 + ur))) * (|q'| * ra') + (|q| * ra) * (|q'| * (ra' * (1 + ur'))) +
        (|q| * ra) * (|q'| * ra') * (1 + ud)) := by ring
  have hY : |q| * |q'| * ((ra * ra' * D) * ((1 + ur) + (1 + ur') + (1 + ud))) ≤
      D * ((2 * b' * hh) * (b * hh') + (b * hh) * (2 * b' * hh') +
        (b * hh) * (b * hh') * (1 + ud)) := by
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add P1 P2) P3) hD
  have hY2 : D * ((2 * b' * hh) * (b * hh') + (b * hh) * (2 * b' * hh') +
        (b * hh) * (b * hh') * (1 + ud)) =
      4 * (b * b') * (hh * hh' * D) + (b * b) * (hh * hh' * D) + (b * b) * (hh * hh' * D2) := by
    rw [← hD2]; ring
  have hbb2 : (b * b) * (hh * hh' * D) ≤ (b * b') * (hh * hh' * D) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbb hb)
      (mul_nonneg (mul_nonneg hh0 hh0') hD)
  have hXY : |q| * |q'| * ((Wr * Wr' * E) * S1) ≤
      (a * a) * (4 * (hh * hh' * TA) + 4 * (hh * hh' * TB)) := by
    have : |q| * |q'| * ((Wr * Wr' * E) * S1) = (|q| * Wr) * (|q'| * Wr') * (E * S1) := by ring
    rw [this]
    refine hXX.trans (le_of_eq ?_)
    ring
  have hCM : 0 ≤ C * M := mul_nonneg hC hM
  have hfin : |q| * |q'| * ((Wr * Wr' * E) * S1 + (ra * ra' * D) * ((1 + ur) + (1 + ur') + (1 + ud))) ≤
      (a * a) * (4 * (hh * hh' * TA) + 4 * (hh * hh' * TB)) + (b * b') * (5 * (hh * hh' * D)) +
        (b * b) * (hh * hh' * D2) := by
    rw [mul_add]
    have := add_le_add hXY (hY.trans (le_of_eq hY2))
    linarith [hbb2]
  calc |q| * |q'| * (C * M * ((Wr * Wr' * E) * S1 +
        (ra * ra' * D) * ((1 + ur) + (1 + ur') + (1 + ud))))
      = C * M * (|q| * |q'| * ((Wr * Wr' * E) * S1 +
        (ra * ra' * D) * ((1 + ur) + (1 + ur') + (1 + ud)))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hfin hCM

/-- **Almost everywhere domination of the tested difference covariance.** -/
theorem ipsiDiff_tested_dominated (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ)
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
            arrSd (fun i j => ∫ ω, hairerIPsiPsiField N (![ξ, ξ'] i) x ω q.1 *
              hairerIPsiPsiField N (![ξ, ξ'] j) x ω q.2 ∂P)| ≤
          C * max ε ε' ^ (2 * θ) *
            (((t ^ (1 / 4 : ℝ)) ^ γ * (t ^ (1 / 4 : ℝ)) ^ γ) *
                (4 * (ipsiWeightedKernel t x q.1 * ipsiWeightedKernel t x q.2 *
                  ((1 + torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj x) ^ (-(p + 2 * θ))) *
                    (1 + torusParabolicSize (spaceTimeProj q.2 - spaceTimeProj x) ^ (-p)))) +
                 4 * (ipsiWeightedKernel t x q.1 * ipsiWeightedKernel t x q.2 *
                  ((1 + torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj x) ^ (-p)) *
                    (1 + torusParabolicSize (spaceTimeProj q.2 - spaceTimeProj x) ^
                      (-(p + 2 * θ)))))) +
              ((t ^ (1 / 4 : ℝ)) ^ ((3 - δ) / 2) * (t ^ (1 / 4 : ℝ)) ^ ((3 - δ) / 2 - 2 * θ)) *
                (5 * (ipsiWeightedKernel t x q.1 * ipsiWeightedKernel t x q.2 *
                  torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj q.2) ^ (-(1 : ℝ)))) +
              ((t ^ (1 / 4 : ℝ)) ^ ((3 - δ) / 2) * (t ^ (1 / 4 : ℝ)) ^ ((3 - δ) / 2)) *
                (ipsiWeightedKernel t x q.1 * ipsiWeightedKernel t x q.2 *
                  torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj q.2) ^ (-(1 + 2 * θ)))) := by
  obtain ⟨C, hC, hcov⟩ := ipsiMix_sd_abs_le.{u} N hρ hρ' hθ hθ4 hp hp1 hγ hγ1 hγθ hδ hδ1 hθδ
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
  have hlg : 0 ≤ l ^ γ := Real.rpow_nonneg hlam.le _
  have hla : 0 ≤ l ^ ((3 - δ) / 2) := Real.rpow_nonneg hlam.le _
  have hn1 := parabolicNorm_nonneg (y - x)
  have hn2 := parabolicNorm_nonneg (y' - x)
  have hE1 : 0 ≤ 1 + e1 ^ (-p) := by have := Real.rpow_nonneg p1.le (-p); linarith
  have hE2 : 0 ≤ 1 + e2 ^ (-p) := by have := Real.rpow_nonneg p2.le (-p); linarith
  have hS1 : 0 ≤ (1 + e1 ^ (-(2 * θ))) + (1 + e2 ^ (-(2 * θ))) := by
    have a1 := Real.rpow_nonneg p1.le (-(2 * θ)); have a2 := Real.rpow_nonneg p2.le (-(2 * θ))
    linarith
  have hD0 : 0 ≤ d ^ (-(1 : ℝ)) := Real.rpow_nonneg p3.le _
  have hD2 : d ^ (-(1 : ℝ)) * d ^ (-(2 * θ)) = d ^ (-(1 + 2 * θ)) := by
    rw [← Real.rpow_add p3]; congr 1; ring
  exact ipsiDiff_pointwise_alg (q := parabolicSemigroup.kernel t x y)
    (q' := parabolicSemigroup.kernel t x y') (hC := hC)
    (hM := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _)
    (hWr' := mul_nonneg (Real.rpow_nonneg hn2 _) (add_nonneg zero_le_one hn2)) (hE := mul_nonneg hE1 hE2)
    (hS1 := hS1) (hra' := Real.rpow_nonneg hn2 _) (hur' := Real.rpow_nonneg hn2 _)
    (hud := Real.rpow_nonneg p3.le _) (hD := hD0)
    (hh0 := ipsiWeightedKernel_nonneg t x y) (hh0' := ipsiWeightedKernel_nonneg t x y')
    (ha := hlg) (hb := hla) (hbb := hll) (hc := hc)
    (hES := ipsi_theta_comb_le (t := 2 * θ) p1 p2 hp.le (by linarith)) (hD2 := hD2)
    (hW := mk y hW1) (hW' := mk y' hW2) (hV := mk y (mk2 r1 hV1 hU1)) (hV0 := mk y hV1)
    (hV' := mk y' (mk2 r2 hV2 hU2)) (hV0' := mk y' hV2)

end RegularityStructures.Phi43

end
