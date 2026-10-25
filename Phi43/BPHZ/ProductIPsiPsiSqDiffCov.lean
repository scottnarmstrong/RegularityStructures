/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductIPsiPsiDiffSd
public import Phi43.BPHZ.ProductIPsiPsiSqDiffIdentity
import Mathlib.Tactic

/-!
# The pointwise bound of the second difference `Δ e` for `I(Ψ)(Ψ² - c₁)`

`e_{ij} = 2 B_ij Q_ij² + 4 A_i A'_j Q_ij + 4 R_ij R'_ij Q_ij` (`hairerIPsiPsiSqField_mix_integral_mul`),
each factor an array in ratio form, so that
`|Δ e| ≤ C m^(2θ) (X₀ D ((1 + e₁^(-2θ)) + (1 + e₂^(-2θ)) + (1 + d^(-2θ))) +
  a D² ((1 + r^(-2θ)) + (1 + r'^(-2θ)) + (1 + d^(-2θ))))` (`ipsiMixSq_sd_abs_le`), where
`X₀ = W W' (1 + e₁^(-p)) (1 + e₂^(-p))`, `a = r^α r'^α`, `D = d^(-1)`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The bound of `Δ e` for `e = 2 B Q² + 4 A A' Q + 4 R R' Q` through the array calculus. -/
theorem ipsiSq_e_sd_le {e rowA colA B Q R R' : Fin 2 → Fin 2 → ℝ}
    {bA bA' bB bQ bR bR' s1 s2 sB sQ s3 s4 : ℝ}
    (hrow : IsArrR rowA bA s1) (hcol : IsArrR colA bA' s2) (hB : IsArrR B bB sB)
    (hQ : IsArrR Q bQ sQ) (hR : IsArrR R bR s3) (hR' : IsArrR R' bR' s4)
    (he : ∀ i j, e i j = 2 * B i j * Q i j ^ 2 + 4 * (rowA i j * colA i j * Q i j) +
      4 * (R i j * R' i j * Q i j)) :
    |arrSd e| ≤ 2 * (16 * bB * (16 * bQ * bQ)) * ((sB + (sQ + sQ) / 2) / 2) ^ 2 +
      4 * (16 * (16 * bA * bA') * bQ) * (((s1 + s2) / 2 + sQ) / 2) ^ 2 +
      4 * (16 * (16 * bR * bR') * bQ) * (((s3 + s4) / 2 + sQ) / 2) ^ 2 := by
  have m1 := (hB.mul (hQ.mul hQ)).to_isArr
  have m2 := ((hrow.mul hcol).mul hQ).to_isArr
  have m3 := ((hR.mul hR').mul hQ).to_isArr
  have a1 := m1.const_mul 2
  have a2 := m2.const_mul 4
  have a3 := m3.const_mul 4
  have a123 := a1.add (a2.add a3)
  have hfun : e = fun i j => 2 * (B i j * (Q i j * Q i j)) +
      (4 * ((rowA i j * colA i j) * Q i j) + 4 * ((R i j * R' i j) * Q i j)) :=
    funext fun i => funext fun j => by rw [he i j]; ring
  rw [hfun]
  have h2 : |(2 : ℝ)| = 2 := abs_of_pos (by norm_num)
  have h4 : |(4 : ℝ)| = 4 := abs_of_pos (by norm_num)
  refine a123.2.2.2.trans (le_of_eq ?_)
  rw [h2, h4]
  ring

/-- Pure algebra: the three array terms against the ratio bounds. -/
theorem ipsiMixSq_alg {Cp CQ CB W W' E1 E2 a D σ1 σ2 σr σr' σd ς1 ς2 sB sQ : ℝ}
    (hCQ : 0 ≤ CQ) (hCB : 0 ≤ CB) (hW : 0 ≤ W) (hW' : 0 ≤ W') (hE1 : 0 ≤ E1)
    (hE2 : 0 ≤ E2) (ha : 0 ≤ a) (hD : 0 ≤ D) (hς1 : 0 ≤ ς1) (hς2 : 0 ≤ ς2) (hsB : 0 ≤ sB)
    (hsQ : 0 ≤ sQ) (h1 : ς1 ≤ σ1) (h2 : ς2 ≤ σ2) (hB : sB ≤ σr + σr') (hQ : sQ ≤ σd) :
    2 * (16 * (CB * a) * (16 * (CQ * D) * (CQ * D))) * ((sB + (sQ + sQ) / 2) / 2) ^ 2 +
      4 * (16 * (16 * (Cp * (3 * CQ) * W * E1) * (Cp * (3 * CQ) * W' * E2)) * (CQ * D)) *
        (((ς1 + ς2) / 2 + sQ) / 2) ^ 2 +
      4 * (16 * (16 * (Cp * CQ * W * E2) * (Cp * CQ * W' * E1)) * (CQ * D)) *
        (((ς2 + ς1) / 2 + sQ) / 2) ^ 2 ≤
    10240 * Cp ^ 2 * CQ ^ 3 * (W * W' * (E1 * E2) * D) * (σ1 ^ 2 + σ2 ^ 2 + σd ^ 2) +
      512 * CB * CQ ^ 2 * (a * (D * D)) * (σr ^ 2 + σr' ^ 2 + σd ^ 2) := by
  have hσ1 : ς1 ^ 2 ≤ σ1 ^ 2 := pow_le_pow_left₀ hς1 h1 2
  have hσ2 : ς2 ^ 2 ≤ σ2 ^ 2 := pow_le_pow_left₀ hς2 h2 2
  have hσd : sQ ^ 2 ≤ σd ^ 2 := pow_le_pow_left₀ hsQ hQ 2
  have hσB : sB ^ 2 ≤ (σr + σr') ^ 2 := pow_le_pow_left₀ hsB hB 2
  have hb : (((ς1 + ς2) / 2 + sQ) / 2) ^ 2 ≤ σ1 ^ 2 + σ2 ^ 2 + σd ^ 2 := by
    have k1 := ipsi_avg_sq_le (a := (ς1 + ς2) / 2) (b := sQ)
    have k2 := ipsi_avg_sq_le (a := ς1) (b := ς2)
    have k3 : sQ ^ 2 ≤ σd ^ 2 := hσd
    have k4 : 0 ≤ σ1 ^ 2 := sq_nonneg _
    have k5 : 0 ≤ σ2 ^ 2 := sq_nonneg _
    have k6 : 0 ≤ σd ^ 2 := sq_nonneg _
    linarith only [k1, k2, k3, hσ1, hσ2, k4, k5, k6]
  have hb' : (((ς2 + ς1) / 2 + sQ) / 2) ^ 2 ≤ σ1 ^ 2 + σ2 ^ 2 + σd ^ 2 := by
    have e : (ς2 + ς1) / 2 = (ς1 + ς2) / 2 := by ring
    rw [e]; exact hb
  have hc : ((sB + (sQ + sQ) / 2) / 2) ^ 2 ≤ σr ^ 2 + σr' ^ 2 + σd ^ 2 := by
    have e : (sB + (sQ + sQ) / 2) / 2 = (sB + sQ) / 2 := by ring
    rw [e]
    have k1 := ipsi_avg_sq_le (a := sB) (b := sQ)
    have k2 : (σr + σr') ^ 2 ≤ 2 * σr ^ 2 + 2 * σr' ^ 2 := by
      nlinarith only [sq_nonneg (σr - σr')]
    have k4 : 0 ≤ σr ^ 2 := sq_nonneg _
    have k5 : 0 ≤ σr' ^ 2 := sq_nonneg _
    have k6 : 0 ≤ σd ^ 2 := sq_nonneg _
    linarith only [k1, k2, hσB, hσd, k4, k5, k6]
  have X0 : 0 ≤ Cp ^ 2 * CQ ^ 3 * (W * W' * (E1 * E2) * D) := by positivity
  have Y0 : 0 ≤ CB * CQ ^ 2 * (a * (D * D)) := by positivity
  have e1 : 4 * (16 * (16 * (Cp * (3 * CQ) * W * E1) * (Cp * (3 * CQ) * W' * E2)) * (CQ * D)) *
        (((ς1 + ς2) / 2 + sQ) / 2) ^ 2 +
      4 * (16 * (16 * (Cp * CQ * W * E2) * (Cp * CQ * W' * E1)) * (CQ * D)) *
        (((ς2 + ς1) / 2 + sQ) / 2) ^ 2 =
      9216 * (Cp ^ 2 * CQ ^ 3 * (W * W' * (E1 * E2) * D)) * (((ς1 + ς2) / 2 + sQ) / 2) ^ 2 +
      1024 * (Cp ^ 2 * CQ ^ 3 * (W * W' * (E1 * E2) * D)) * (((ς2 + ς1) / 2 + sQ) / 2) ^ 2 := by
    ring
  have e2 : 2 * (16 * (CB * a) * (16 * (CQ * D) * (CQ * D))) * ((sB + (sQ + sQ) / 2) / 2) ^ 2 =
      512 * (CB * CQ ^ 2 * (a * (D * D))) * ((sB + (sQ + sQ) / 2) / 2) ^ 2 := by ring
  have t1 := mul_le_mul_of_nonneg_left hb (mul_nonneg (by norm_num : (0 : ℝ) ≤ 9216) X0)
  have t2 := mul_le_mul_of_nonneg_left hb' (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1024) X0)
  have t3 := mul_le_mul_of_nonneg_left hc (mul_nonneg (by norm_num : (0 : ℝ) ≤ 512) Y0)
  rw [e2]
  have e3 : 10240 * Cp ^ 2 * CQ ^ 3 * (W * W' * (E1 * E2) * D) * (σ1 ^ 2 + σ2 ^ 2 + σd ^ 2) =
      10240 * (Cp ^ 2 * CQ ^ 3 * (W * W' * (E1 * E2) * D)) * (σ1 ^ 2 + σ2 ^ 2 + σd ^ 2) := by ring
  have e4 : 512 * CB * CQ ^ 2 * (a * (D * D)) * (σr ^ 2 + σr' ^ 2 + σd ^ 2) =
      512 * (CB * CQ ^ 2 * (a * (D * D))) * (σr ^ 2 + σr' ^ 2 + σd ^ 2) := by ring
  rw [e3, e4]
  linarith only [t1, t2, t3, e1]

/-- Pure algebra: squares of the ratios against the weights `1 + s^(-2θ)`. -/
theorem ipsiMixSq_weighted_sq_alg {K1 K2 X Y M u1 u2 ur ur' ud σ1 σ2 σr σr' σd : ℝ}
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hM : 0 ≤ M)
    (hu1 : 0 ≤ u1) (hu2 : 0 ≤ u2) (hur : 0 ≤ ur) (hur' : 0 ≤ ur') (hud : 0 ≤ ud)
    (h1 : σ1 ^ 2 ≤ 2 * M * (1 + u1)) (h2 : σ2 ^ 2 ≤ 2 * M * (1 + u2))
    (h3 : σr ^ 2 ≤ 2 * M * (1 + ur)) (h4 : σr' ^ 2 ≤ 2 * M * (1 + ur'))
    (h5 : σd ^ 2 ≤ 2 * M * (1 + ud)) :
    K1 * X * (σ1 ^ 2 + σ2 ^ 2 + σd ^ 2) + K2 * Y * (σr ^ 2 + σr' ^ 2 + σd ^ 2) ≤
      (2 * K1 + 2 * K2) * M *
        (X * ((1 + u1) + (1 + u2) + (1 + ud)) + Y * ((1 + ur) + (1 + ur') + (1 + ud))) := by
  have a0 : 0 ≤ K1 * X := mul_nonneg hK1 hX
  have b0 : 0 ≤ K2 * Y := mul_nonneg hK2 hY
  have t1 := mul_le_mul_of_nonneg_left (add_le_add (add_le_add h1 h2) h5) a0
  have t2 := mul_le_mul_of_nonneg_left (add_le_add (add_le_add h3 h4) h5) b0
  have S1 : 0 ≤ (1 + u1) + (1 + u2) + (1 + ud) := by linarith
  have S2 : 0 ≤ (1 + ur) + (1 + ur') + (1 + ud) := by linarith
  have p1 : 0 ≤ 2 * K2 * M * X * ((1 + u1) + (1 + u2) + (1 + ud)) := by positivity
  have p2 : 0 ≤ 2 * K1 * M * Y * ((1 + ur) + (1 + ur') + (1 + ud)) := by positivity
  nlinarith only [t1, t2, p1, p2]

end RegularityStructures.Phi43

end
