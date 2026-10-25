/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.CrossMollifierDifference
public import Phi43.BPHZ.ProductIPsiPsiDiffFour
import Mathlib.Tactic

/-!
# The `2 × 2` table of cross covariances as an array in ratio form

For `m = max ε ε'` and `σ(s) = m^θ (1 + s^(-θ))`, the array `(i, j) ↦ Q_{ij}(z)` of the two models
`(ρ, ε)`, `(ρ', ε')` satisfies `IsArrR (C s(z)^(-1)) (min 1 σ(s(z)))` (`qMix_isArrR`):
`|Q_22| ≲ s⁻¹`, first differences `≲ s⁻¹ min 1 σ`, second difference `≲ s⁻¹ (min 1 σ)²`.
-/

@[expose] public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

/-- A capped bound: `f ≤ C₁ b σ^k` and `f ≤ C₂ b` give `f ≤ max C₁ C₂ b (min 1 σ)^k`. -/
theorem cap_le {f b σ C₁ C₂ : ℝ} (k : ℕ) (hb : 0 ≤ b) (hσ : 0 ≤ σ) (h1 : f ≤ C₁ * b * σ ^ k)
    (h2 : f ≤ C₂ * b) : f ≤ max C₁ C₂ * b * (min 1 σ) ^ k := by
  rcases le_total σ 1 with h | h
  · rw [min_eq_right h]
    refine h1.trans ?_
    have : 0 ≤ b * σ ^ k := mul_nonneg hb (pow_nonneg hσ _)
    nlinarith [le_max_left C₁ C₂]
  · rw [min_eq_left h, one_pow, mul_one]
    refine h2.trans ?_
    nlinarith [le_max_right C₁ C₂]

/-- The ratio `σ(s) = m^θ (1 + s^(-θ))`. -/
noncomputable def ipsiRatio (m θ s : ℝ) : ℝ := m ^ θ * (1 + s ^ (-θ))

theorem ipsiRatio_nonneg (m θ s : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) : 0 ≤ ipsiRatio m θ s := by
  unfold ipsiRatio
  have := Real.rpow_nonneg hs (-θ)
  have := Real.rpow_nonneg hm θ
  positivity

/-- The algebra of `qMix_isArrR`. -/
theorem qmix_table_alg {a b c d C0 C1 C2 C3 S σ : ℝ} (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1)
    (hC2 : 0 ≤ C2) (hC3 : 0 ≤ C3) (hS : 0 ≤ S) (hσ : 0 ≤ σ)
    (c00 : |a| ≤ C0 * S) (c01 : |a + b| ≤ C0 * S) (c10 : |a + c| ≤ C0 * S)
    (c11 : |a + b + c + d| ≤ C0 * S) (l1 : |a + b - c - d| ≤ C1 * S * σ)
    (l0 : |a - c| ≤ C1 * S * σ) (r1 : |a - b + c - d| ≤ C2 * S * σ) (r0 : |a - b| ≤ C2 * S * σ)
    (s2 : |a - b - c + d| ≤ C3 * S * σ ^ 2) :
    |d| ≤ (2 * C1 + 2 * C2 + C3 + 9 * C0) * S ∧
    |b - d| ≤ (2 * C1 + 2 * C2 + C3 + 9 * C0) * S * min 1 σ ∧
    |c - d| ≤ (2 * C1 + 2 * C2 + C3 + 9 * C0) * S * min 1 σ ∧
    |a - b - c + d| ≤ (2 * C1 + 2 * C2 + C3 + 9 * C0) * S * (min 1 σ) ^ 2 := by
  have lsd : ∀ {u K : ℝ}, |u| ≤ K → -K ≤ u ∧ u ≤ K := fun h => abs_le.1 h
  obtain ⟨c00a, c00b⟩ := lsd c00
  obtain ⟨c01a, c01b⟩ := lsd c01
  obtain ⟨c10a, c10b⟩ := lsd c10
  obtain ⟨c11a, c11b⟩ := lsd c11
  have hCS : 0 ≤ C0 * S := mul_nonneg hC0 hS
  have hdb : |d| ≤ 4 * (C0 * S) := by
    rw [abs_le]; constructor <;> linarith only [c00a, c00b, c01a, c01b, c10a, c10b, c11a, c11b]
  have hbd : |b - d| ≤ 6 * (C0 * S) := by
    rw [abs_le]; constructor <;> linarith only [c00a, c00b, c01a, c01b, c10a, c10b, c11a, c11b]
  have hcd : |c - d| ≤ 6 * (C0 * S) := by
    rw [abs_le]; constructor <;> linarith only [c00a, c00b, c01a, c01b, c10a, c10b, c11a, c11b]
  have hsd : |a - b - c + d| ≤ 9 * (C0 * S) := by
    rw [abs_le]; constructor <;> linarith only [c00a, c00b, c01a, c01b, c10a, c10b, c11a, c11b]
  have hbd1 : |b - d| ≤ (2 * C1) * S * σ ^ 1 := by
    have h1 := abs_sub (a + b - c - d) (a - c)
    have e : b - d = (a + b - c - d) - (a - c) := by ring
    rw [e, pow_one]; linarith [h1, l1, l0]
  have hcd1 : |c - d| ≤ (2 * C2) * S * σ ^ 1 := by
    have h1 := abs_sub (a - b + c - d) (a - b)
    have e : c - d = (a - b + c - d) - (a - b) := by ring
    rw [e, pow_one]; linarith [h1, r1, r0]
  have k1 := cap_le 1 hS hσ hbd1 (show |b - d| ≤ (6 * C0) * S by linarith)
  have k2 := cap_le 1 hS hσ hcd1 (show |c - d| ≤ (6 * C0) * S by linarith)
  have k3 := cap_le 2 hS hσ s2 (show |a - b - c + d| ≤ (9 * C0) * S by linarith)
  have cm : 0 ≤ min 1 σ := le_min zero_le_one hσ
  have h1' : max (2 * C1) (6 * C0) ≤ 2 * C1 + 2 * C2 + C3 + 9 * C0 := max_le (by linarith) (by linarith)
  have h2' : max (2 * C2) (6 * C0) ≤ 2 * C1 + 2 * C2 + C3 + 9 * C0 := max_le (by linarith) (by linarith)
  have h3' : max C3 (9 * C0) ≤ 2 * C1 + 2 * C2 + C3 + 9 * C0 := max_le (by linarith) (by linarith)
  have mS : ∀ {M : ℝ}, 0 ≤ M → ∀ {K : ℝ}, K ≤ M → K * S ≤ M * S := fun _ _ h =>
    mul_le_mul_of_nonneg_right h hS
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine hdb.trans ?_
    linarith only [mul_nonneg hC0 hS, mul_nonneg hC1 hS, mul_nonneg hC2 hS, mul_nonneg hC3 hS]
  · rw [pow_one] at k1
    exact k1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1' hS) cm)
  · rw [pow_one] at k2
    exact k2.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2' hS) cm)
  · exact k3.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3' hS)
      (sq_nonneg (min 1 σ)))

theorem ipsi_gain_one {m θ sz : ℝ} (hm0 : 0 ≤ m) (hz : 0 < sz) :
    m ^ θ * sz ^ (-1 - θ) ≤ sz ^ (-(1 : ℝ)) * ipsiRatio m θ sz := by
  have hs0 : 0 ≤ sz ^ (-(1 : ℝ)) := Real.rpow_nonneg hz.le _
  have : sz ^ (-1 - θ) = sz ^ (-(1 : ℝ)) * sz ^ (-θ) := by
    rw [← Real.rpow_add hz]; congr 1
  rw [this]; unfold ipsiRatio
  have h1 := Real.rpow_nonneg hm0 θ
  linarith [mul_nonneg hs0 h1]

theorem ipsi_gain_two {m θ sz : ℝ} (hm0 : 0 ≤ m) (hz : 0 < sz) :
    m ^ (2 * θ) * sz ^ (-1 - 2 * θ) ≤ sz ^ (-(1 : ℝ)) * ipsiRatio m θ sz ^ 2 := by
  have hs0 : 0 ≤ sz ^ (-(1 : ℝ)) := Real.rpow_nonneg hz.le _
  have hg : 0 ≤ sz ^ (-θ) := Real.rpow_nonneg hz.le _
  have e1 : sz ^ (-1 - 2 * θ) = sz ^ (-(1 : ℝ)) * (sz ^ (-θ)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hz.le, ← Real.rpow_add hz]; congr 1; push_cast; ring
  have e2 : m ^ (2 * θ) = (m ^ θ) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm0]; congr 1; push_cast; ring
  rw [e1, e2]; unfold ipsiRatio
  have h2 : 0 ≤ sz ^ (-(1 : ℝ)) * (m ^ θ) ^ 2 * (1 + 2 * sz ^ (-θ)) := by positivity
  linarith [h2]

/-- **The table of cross covariances in ratio form.** -/
theorem qMix_isArrR (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    (hρ' : IsMollifier ρ') {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε ε' : ℝ}, 0 < ε → ε ≤ 1 → 0 < ε' → ε' ≤ 1 →
      ∀ z : SpaceTime, 0 < torusParabolicSize z →
        IsArrR (fun i j => qMix N ![ρ, ρ'] ![ε, ε'] i j z) (C * torusParabolicSize z ^ (-(1 : ℝ)))
          (min 1 (ipsiRatio (max ε ε') θ (torusParabolicSize z))) := by
  obtain ⟨C0, hC0, hcomb⟩ := hairerCrossTwo_comb_abs_le N ρ ρ' hρ hρ'
  obtain ⟨C1, hC1, hleft⟩ := hairerCrossTwo_diff_left_abs_le N ρ ρ' hρ hρ' hθ hθ1
  obtain ⟨C2, hC2, hright⟩ := hairerCrossTwo_diff_right_abs_le N ρ ρ' hρ hρ' hθ hθ1
  obtain ⟨C3, hC3, hsec⟩ := hairerCrossTwo_second_diff_abs_le N ρ ρ' hρ hρ' hθ hθ1
  refine ⟨2 * C1 + 2 * C2 + C3 + 9 * C0, by positivity, ?_⟩
  intro ε ε' hε hε1 hε' hε'1 z hz
  have hm0 : 0 ≤ max ε ε' := le_max_of_le_left hε.le
  have c00 := hcomb (s := 0) (t := 0) hε hε1 hε' hε'1 (by simp) (by simp) z hz
  have c01 := hcomb (s := 0) (t := 1) hε hε1 hε' hε'1 (by simp) (by simp) z hz
  have c10 := hcomb (s := 1) (t := 0) hε hε1 hε' hε'1 (by simp) (by simp) z hz
  have c11 := hcomb (s := 1) (t := 1) hε hε1 hε' hε'1 (by simp) (by simp) z hz
  have l0 := hleft (t := 0) hε hε1 hε' hε'1 (by simp) z hz
  have l1 := hleft (t := 1) hε hε1 hε' hε'1 (by simp) z hz
  have r0 := hright (s := 0) hε hε1 hε' hε'1 (by simp) z hz
  have r1 := hright (s := 1) hε hε1 hε' hε'1 (by simp) z hz
  have s2 := hsec hε hε1 hε' hε'1 z hz
  simp only [zero_mul, add_zero, mul_zero, one_mul, mul_one, sub_zero] at c00 c01 c10 c11 l0 l1 r0 r1
  have hs0 : 0 ≤ torusParabolicSize z ^ (-(1 : ℝ)) := Real.rpow_nonneg hz.le _
  have hσ0 : 0 ≤ ipsiRatio (max ε ε') θ (torusParabolicSize z) :=
    ipsiRatio_nonneg _ θ _ hm0 hz.le
  have g1 := ipsi_gain_one (θ := θ) hm0 hz
  have g2 := ipsi_gain_two (θ := θ) hm0 hz
  have step : ∀ {u K C : ℝ}, 0 ≤ C → u ≤ C * (max ε ε') ^ θ * torusParabolicSize z ^ (-1 - θ) →
      u ≤ C * torusParabolicSize z ^ (-(1 : ℝ)) * ipsiRatio (max ε ε') θ (torusParabolicSize z) :=
    fun {u K C} hC h => h.trans (by
      calc C * max ε ε' ^ θ * torusParabolicSize z ^ (-1 - θ)
          = C * (max ε ε' ^ θ * torusParabolicSize z ^ (-1 - θ)) := by ring
        _ ≤ C * (torusParabolicSize z ^ (-(1 : ℝ)) *
              ipsiRatio (max ε ε') θ (torusParabolicSize z)) := mul_le_mul_of_nonneg_left g1 hC
        _ = _ := by ring)
  have s2' : |hairerCrossCovarianceTwo N ρ ε ρ ε z - hairerCrossCovarianceTwo N ρ ε ρ' ε' z -
      hairerCrossCovarianceTwo N ρ' ε' ρ ε z + hairerCrossCovarianceTwo N ρ' ε' ρ' ε' z| ≤
      C3 * torusParabolicSize z ^ (-(1 : ℝ)) *
        ipsiRatio (max ε ε') θ (torusParabolicSize z) ^ 2 := by
    refine s2.trans ?_
    calc C3 * max ε ε' ^ (2 * θ) * torusParabolicSize z ^ (-1 - 2 * θ)
        = C3 * (max ε ε' ^ (2 * θ) * torusParabolicSize z ^ (-1 - 2 * θ)) := by ring
      _ ≤ C3 * (torusParabolicSize z ^ (-(1 : ℝ)) *
            ipsiRatio (max ε ε') θ (torusParabolicSize z) ^ 2) := mul_le_mul_of_nonneg_left g2 hC3
      _ = _ := by ring
  obtain ⟨t1, t2, t3, t4⟩ := qmix_table_alg hC0 hC1 hC2 hC3 hs0 hσ0 c00 c01 c10 c11
    (step (K := 0) hC1 l1) (step (K := 0) hC1 l0) (step (K := 0) hC2 r1) (step (K := 0) hC2 r0) s2'
  have e00 : qMix N ![ρ, ρ'] ![ε, ε'] 0 0 z = hairerCrossCovarianceTwo N ρ ε ρ ε z := by
    simp [qMix]
  have e01 : qMix N ![ρ, ρ'] ![ε, ε'] 0 1 z = hairerCrossCovarianceTwo N ρ ε ρ' ε' z := by
    simp [qMix]
  have e10 : qMix N ![ρ, ρ'] ![ε, ε'] 1 0 z = hairerCrossCovarianceTwo N ρ' ε' ρ ε z := by
    simp [qMix]
  have e11 : qMix N ![ρ, ρ'] ![ε, ε'] 1 1 z = hairerCrossCovarianceTwo N ρ' ε' ρ' ε' z := by
    simp [qMix]
  have cm : 0 ≤ min 1 (ipsiRatio (max ε ε') θ (torusParabolicSize z)) := le_min zero_le_one hσ0
  have cm1 : min 1 (ipsiRatio (max ε ε') θ (torusParabolicSize z)) ≤ 1 := min_le_left _ _
  have hsd : arrSd (fun i j => qMix N ![ρ, ρ'] ![ε, ε'] i j z) =
      hairerCrossCovarianceTwo N ρ ε ρ ε z - hairerCrossCovarianceTwo N ρ ε ρ' ε' z -
      hairerCrossCovarianceTwo N ρ' ε' ρ ε z + hairerCrossCovarianceTwo N ρ' ε' ρ' ε' z := by
    unfold arrSd; simp only [e00, e01, e10, e11]
  refine ⟨cm, cm1, ?_, ?_, ?_, ?_⟩
  · simp only [e11]; exact t1
  · simp only [e01, e11]; exact t2
  · simp only [e10, e11]; exact t3
  · rw [hsd]; exact t4

end RegularityStructures.Phi43

end
