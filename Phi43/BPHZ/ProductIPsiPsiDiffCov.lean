/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductIPsiPsiDiffIdentity
public import Phi43.BPHZ.ProductIPsiPsiDiffPairingArr
public import Phi43.BPHZ.ProductIPsiPsiDiffBVar
public import Phi43.BPHZ.ProductIPsiPsiDiffKernel
public import Phi43.BPHZ.TreeI3Psi2DifferenceTwoChaos
import Mathlib.Tactic

/-!
# The pointwise bound of the second difference `Δe` for `I(Ψ)Ψ`

`e_{ij}(y, y') = E[F_i(y) F_j(y')] = A_i A'_j + B_{ij} Q_{ij}(p - p') + R_{ij} R'_{ij}` and
`E[(F₀ - F₁)(y) (F₀ - F₁)(y')] = Δ e`.  Each factor is an array in ratio form
(`qMix_isArrR`, `ipsi_pairing_isArrR`, `ipsi_B_isArrR`), so `IsArrR.mul` bounds `Δ e`
(`ipsi_e_sd_le`), and the resulting bound is
`|Δ e| ≤ C m^(2θ) (X₀ ((1 + e₁^(-2θ)) + (1 + e₂^(-2θ))) +
  Y₀ ((1 + r^(-2θ)) + (1 + r'^(-2θ)) + (1 + d^(-2θ))))`
(`ipsiMix_sd_abs_le`).
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

theorem IsArrR.diag_row {h : Fin 2 → Fin 2 → ℝ} {b ς : ℝ} (H : IsArrR h b ς) :
    IsArrR (fun i _ => h i i) (3 * b) ς := by
  obtain ⟨c0, c1, h11, h01, h10, hsd⟩ := H
  have bn : 0 ≤ b := (abs_nonneg _).trans h11
  have h2 : ς ^ 2 ≤ ς := by nlinarith
  have hbς : 0 ≤ b * ς := mul_nonneg bn c0
  refine ⟨c0, c1, ?_, ?_, ?_, ?_⟩
  · show |h 1 1| ≤ 3 * b
    linarith
  · show |h 0 0 - h 1 1| ≤ 3 * b * ς
    have e : h 0 0 - h 1 1 = arrSd h + (h 0 1 - h 1 1) + (h 1 0 - h 1 1) := by unfold arrSd; ring
    rw [e]
    have := abs_add_three (arrSd h) (h 0 1 - h 1 1) (h 1 0 - h 1 1)
    have k : b * ς ^ 2 ≤ b * ς := mul_le_mul_of_nonneg_left h2 bn
    linarith
  · show |h 1 1 - h 1 1| ≤ 3 * b * ς
    simp only [sub_self, abs_zero]; positivity
  · show |arrSd (fun i _ => h i i)| ≤ 3 * b * ς ^ 2
    have : arrSd (fun i _ => h i i) = 0 := by unfold arrSd; ring
    rw [this, abs_zero]; positivity

theorem IsArrR.diag_col {h : Fin 2 → Fin 2 → ℝ} {b ς : ℝ} (H : IsArrR h b ς) :
    IsArrR (fun _ j => h j j) (3 * b) ς := by
  obtain ⟨c0, c1, h11, h01, h10, hsd⟩ := H
  have bn : 0 ≤ b := (abs_nonneg _).trans h11
  have h2 : ς ^ 2 ≤ ς := by nlinarith
  have hbς : 0 ≤ b * ς := mul_nonneg bn c0
  refine ⟨c0, c1, ?_, ?_, ?_, ?_⟩
  · show |h 1 1| ≤ 3 * b
    linarith
  · show |h 1 1 - h 1 1| ≤ 3 * b * ς
    simp only [sub_self, abs_zero]; positivity
  · show |h 0 0 - h 1 1| ≤ 3 * b * ς
    have e : h 0 0 - h 1 1 = arrSd h + (h 0 1 - h 1 1) + (h 1 0 - h 1 1) := by unfold arrSd; ring
    rw [e]
    have := abs_add_three (arrSd h) (h 0 1 - h 1 1) (h 1 0 - h 1 1)
    have k : b * ς ^ 2 ≤ b * ς := mul_le_mul_of_nonneg_left h2 bn
    linarith
  · show |arrSd (fun _ j => h j j)| ≤ 3 * b * ς ^ 2
    have : arrSd (fun _ j => h j j) = 0 := by unfold arrSd; ring
    rw [this, abs_zero]; positivity

/-- The bound of `Δ e` for `e = A A' + B Q + R R'` through the array calculus. -/
theorem ipsi_e_sd_le {e rowA colA B Q R R' : Fin 2 → Fin 2 → ℝ}
    {bA bA' bB bQ bR bR' s1 s2 sB sQ s3 s4 : ℝ}
    (hrow : IsArrR rowA bA s1) (hcol : IsArrR colA bA' s2) (hB : IsArrR B bB sB)
    (hQ : IsArrR Q bQ sQ) (hR : IsArrR R bR s3) (hR' : IsArrR R' bR' s4)
    (he : ∀ i j, e i j = rowA i j * colA i j + B i j * Q i j + R i j * R' i j) :
    |arrSd e| ≤ 16 * bA * bA' * ((s1 + s2) / 2) ^ 2 + 16 * bB * bQ * ((sB + sQ) / 2) ^ 2 +
      16 * bR * bR' * ((s3 + s4) / 2) ^ 2 := by
  have m1 := (hrow.mul hcol).to_isArr
  have m2 := (hB.mul hQ).to_isArr
  have m3 := (hR.mul hR').to_isArr
  have a12 := m1.add m2
  have a123 := a12.add m3
  have hfun : e = fun i j => rowA i j * colA i j + B i j * Q i j + R i j * R' i j := funext fun i =>
    funext fun j => he i j
  rw [hfun]
  refine a123.2.2.2.trans (le_of_eq ?_)
  ring

theorem ipsi_ratio_sq_le {m θ s : ℝ} (hm : 0 ≤ m) (hs : 0 < s) :
    ipsiRatio m θ s ^ 2 ≤ 2 * m ^ (2 * θ) * (1 + s ^ (-(2 * θ))) := by
  unfold ipsiRatio
  have hmm : (m ^ θ) ^ 2 = m ^ (2 * θ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm]; congr 1; push_cast; ring
  have hss : (s ^ (-θ)) ^ 2 = s ^ (-(2 * θ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]; congr 1; push_cast; ring
  rw [mul_pow, hmm]
  have h2 : (1 + s ^ (-θ)) ^ 2 ≤ 2 * (1 + (s ^ (-θ)) ^ 2) := by
    linarith [sq_nonneg (1 - s ^ (-θ))]
  rw [hss] at h2
  have := Real.rpow_nonneg hm (2 * θ)
  linarith [mul_le_mul_of_nonneg_left h2 this]

theorem ipsi_avg_sq_le {a b : ℝ} : ((a + b) / 2) ^ 2 ≤ (a ^ 2 + b ^ 2) / 2 := by
  linarith [sq_nonneg (a - b)]

/-- Pure algebra: the three array terms against the ratio bounds. -/
theorem ipsiMix_alg {Cp CQ CB W W' E1 E2 a d1 σ1 σ2 σr σr' σd ς1 ς2 sB sQ : ℝ}
    (hCQ : 0 ≤ CQ) (hCB : 0 ≤ CB) (hW : 0 ≤ W) (hW' : 0 ≤ W') (hE1 : 0 ≤ E1)
    (hE2 : 0 ≤ E2) (ha : 0 ≤ a) (hd : 0 ≤ d1) (hς1 : 0 ≤ ς1) (hς2 : 0 ≤ ς2) (hsB : 0 ≤ sB)
    (hsQ : 0 ≤ sQ) (h1 : ς1 ≤ σ1) (h2 : ς2 ≤ σ2) (hB : sB ≤ σr + σr') (hQ : sQ ≤ σd) :
    16 * (Cp * (3 * CQ) * W * E1) * (Cp * (3 * CQ) * W' * E2) * ((ς1 + ς2) / 2) ^ 2 +
      16 * (CB * a) * (CQ * d1) * ((sB + sQ) / 2) ^ 2 +
      16 * (Cp * CQ * W * E2) * (Cp * CQ * W' * E1) * ((ς2 + ς1) / 2) ^ 2 ≤
    80 * Cp ^ 2 * CQ ^ 2 * (W * W' * (E1 * E2)) * (σ1 ^ 2 + σ2 ^ 2) +
      16 * CB * CQ * (a * d1) * (σr ^ 2 + σr' ^ 2 + σd ^ 2) := by
  have hx : ((ς1 + ς2) / 2) ^ 2 ≤ (σ1 ^ 2 + σ2 ^ 2) / 2 := by
    have : ς1 ^ 2 ≤ σ1 ^ 2 := pow_le_pow_left₀ hς1 h1 2
    have : ς2 ^ 2 ≤ σ2 ^ 2 := pow_le_pow_left₀ hς2 h2 2
    linarith [sq_nonneg (ς1 - ς2)]
  have hx' : ((ς2 + ς1) / 2) ^ 2 ≤ (σ1 ^ 2 + σ2 ^ 2) / 2 := by
    have e : (ς2 + ς1) / 2 = (ς1 + ς2) / 2 := by ring
    rw [e]; exact hx
  have hy : ((sB + sQ) / 2) ^ 2 ≤ σr ^ 2 + σr' ^ 2 + σd ^ 2 := by
    have c1 : sB ^ 2 ≤ (σr + σr') ^ 2 := pow_le_pow_left₀ hsB hB 2
    have c2 : sQ ^ 2 ≤ σd ^ 2 := pow_le_pow_left₀ hsQ hQ 2
    linarith [sq_nonneg (sB - sQ), sq_nonneg (σr - σr'), sq_nonneg σd]
  have X0 : 0 ≤ Cp ^ 2 * CQ ^ 2 * (W * W' * (E1 * E2)) := by positivity
  have Y0 : 0 ≤ CB * CQ * (a * d1) := by positivity
  have e1 : 16 * (Cp * (3 * CQ) * W * E1) * (Cp * (3 * CQ) * W' * E2) * ((ς1 + ς2) / 2) ^ 2 +
      16 * (Cp * CQ * W * E2) * (Cp * CQ * W' * E1) * ((ς2 + ς1) / 2) ^ 2 =
      144 * (Cp ^ 2 * CQ ^ 2 * (W * W' * (E1 * E2))) * ((ς1 + ς2) / 2) ^ 2 +
      16 * (Cp ^ 2 * CQ ^ 2 * (W * W' * (E1 * E2))) * ((ς2 + ς1) / 2) ^ 2 := by ring
  have e2 : 16 * (CB * a) * (CQ * d1) * ((sB + sQ) / 2) ^ 2 =
      16 * (CB * CQ * (a * d1)) * ((sB + sQ) / 2) ^ 2 := by ring
  have t1 := mul_le_mul_of_nonneg_left hx (mul_nonneg (by norm_num : (0 : ℝ) ≤ 144) X0)
  have t2 := mul_le_mul_of_nonneg_left hx' (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) X0)
  have t3 := mul_le_mul_of_nonneg_left hy (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) Y0)
  linarith [t1, t2, t3, e1, e2]

/-- Pure algebra: squares of the ratios against the weights `1 + s^(-2θ)`. -/
theorem ipsiMix_weighted_sq_alg {Cp CQ CB X Y M u1 u2 ur ur' ud σ1 σ2 σr σr' σd : ℝ}
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hCB : 0 ≤ CB) (hCQ : 0 ≤ CQ) (hM : 0 ≤ M)
    (hu1 : 0 ≤ u1) (hu2 : 0 ≤ u2) (hur : 0 ≤ ur) (hur' : 0 ≤ ur') (hud : 0 ≤ ud)
    (h1 : σ1 ^ 2 ≤ 2 * M * (1 + u1)) (h2 : σ2 ^ 2 ≤ 2 * M * (1 + u2))
    (h3 : σr ^ 2 ≤ 2 * M * (1 + ur)) (h4 : σr' ^ 2 ≤ 2 * M * (1 + ur'))
    (h5 : σd ^ 2 ≤ 2 * M * (1 + ud)) :
    80 * Cp ^ 2 * CQ ^ 2 * X * (σ1 ^ 2 + σ2 ^ 2) + 16 * CB * CQ * Y * (σr ^ 2 + σr' ^ 2 + σd ^ 2) ≤
      (160 * Cp ^ 2 * CQ ^ 2 + 32 * CB * CQ) * M *
        (X * ((1 + u1) + (1 + u2)) + Y * ((1 + ur) + (1 + ur') + (1 + ud))) := by
  have a0 : 0 ≤ 80 * Cp ^ 2 * CQ ^ 2 * X := by positivity
  have b0 : 0 ≤ 16 * CB * CQ * Y := by positivity
  have t1 := mul_le_mul_of_nonneg_left (add_le_add h1 h2) a0
  have t2 := mul_le_mul_of_nonneg_left (add_le_add (add_le_add h3 h4) h5) b0
  have S1 : 0 ≤ (1 + u1) + (1 + u2) := by linarith
  have S2 : 0 ≤ (1 + ur) + (1 + ur') + (1 + ud) := by linarith
  have p1 : 0 ≤ 32 * CB * CQ * M * X * ((1 + u1) + (1 + u2)) := by positivity
  have p2 : 0 ≤ 160 * Cp ^ 2 * CQ ^ 2 * M * Y * ((1 + ur) + (1 + ur') + (1 + ud)) := by positivity
  linarith [t1, t2, p1, p2]

end RegularityStructures.Phi43

end
