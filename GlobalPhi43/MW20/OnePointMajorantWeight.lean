module

public import GlobalPhi43.MW20.ReciprocalScaleMonomial
public import GlobalPhi43.MW20.OnePointBudgetScale

/-! Reciprocal-scale weight of the complete one-point majorant. -/

public section

namespace GlobalPhi43.MW20

/-- Every term of the majorant retains its parent amplitude and
is paid by its actual weighted norm or M on the reciprocal-scale range. -/
theorem sourceOnePointMajorant_weight {ε d M H Hv HU Hν N c : ℝ}
    (hd : 0 < d) (hM : 0 < M) (hsmall : ε < 1 / 14)
    (hH : 0 ≤ H) (hHv : 0 ≤ Hv) (hHU : 0 ≤ HU) (hHν : 0 ≤ Hν)
    (hN : 0 ≤ N) (hc : 0 ≤ c) (hscale : d * M ≤ 1) :
    d ^ (3 / 2 - 5 * ε) * sourceOnePointMajorant ε d M H Hv HU Hν N c ≤
      M + c * (d ^ (1 - 2 * ε) * H + 3 * d ^ (1 / 2 - 3 * ε) * Hv +
        d ^ (3 / 2 - 5 * ε) * HU + d ^ (3 / 2 - 5 * ε) * Hν + d * N + 5 * M) := by
  have hnorm (l a p X : ℝ) (hp : 0 ≤ p) (hX : 0 ≤ X)
      (he : (3 / 2 : ℝ) - 5 * ε + l = a + p) :=
    reciprocal_scale_norm_monomial hd hM hp hX hscale he
  have h₁ := hnorm (1 + 2 * ε) (1 - 2 * ε) (3 / 2 - ε) H (by linarith) hH (by ring)
  have h₂ := hnorm (1 - 2 * ε) (1 / 2 - 3 * ε) (2 - 4 * ε) Hv
    (by linarith) hHv (by ring)
  have h₃ := hnorm (1 - 2 * ε) (3 / 2 - 5 * ε) (1 - 2 * ε) (HU + Hν)
    (by linarith) (add_nonneg hHU hHν) (by ring)
  have h₄ := hnorm (1 / 2 + 3 * ε) 1 (1 - 2 * ε) N
    (by linarith) hN (by ring)
  have h₅ := hnorm 0 (1 / 2 - 3 * ε) (1 - 2 * ε) Hv
    (by linarith) hHv (by ring)
  simp only [Real.rpow_zero, one_mul, Real.rpow_one] at h₄ h₅
  have htree (l p : ℝ) (hp : 0 ≤ p) (he : (3 / 2 : ℝ) - 5 * ε + l = p) :
      d ^ (3 / 2 - 5 * ε) * (d ^ l * M ^ (1 + p)) ≤ M := by
    have hh := parent_tree_weight hd hM (by norm_num : (0 : ℝ) ≤ 1)
      (le_refl 1) hp hscale
    rw [← mul_assoc, ← Real.rpow_add hd, he]
    simpa only [one_mul] using hh
  have ht₀ := htree (1 / 2 + 5 * ε) 2 (by norm_num) (by ring)
  have ht₁ := htree (4 * ε) (3 / 2 - ε) (by linarith) (by ring)
  have ht₂ := htree (1 / 2 + ε) (2 - 4 * ε) (by linarith) (by ring)
  have ht₃ := htree (1 - 2 * ε) (5 / 2 - 7 * ε) (by linarith) (by ring)
  have ht₄ := htree 0 (3 / 2 - 5 * ε) (by linarith) (by ring)
  norm_num only [Real.rpow_zero, one_mul] at ht₄
  norm_num only [show (1 : ℝ) + 2 = 3 by norm_num] at ht₀
  rw [Real.rpow_ofNat] at ht₀
  have hm₁ : (1 : ℝ) + (3 / 2 - ε) = 5 / 2 - ε := by ring
  have hm₂ : (1 : ℝ) + (2 - 4 * ε) = 3 - 4 * ε := by ring
  have hm₃ : (1 : ℝ) + (5 / 2 - 7 * ε) = 7 / 2 - 7 * ε := by ring
  have hm₄ : (1 : ℝ) + (3 / 2 - 5 * ε) = 5 / 2 - 5 * ε := by ring
  rw [hm₁] at ht₁
  rw [hm₂] at ht₂
  rw [hm₃] at ht₃
  rw [hm₄] at ht₄
  unfold sourceOnePointMajorant sourceFirstProductScale sourceSecondProductScale
  nlinarith only [ht₀, mul_le_mul_of_nonneg_left h₁ hc,
    mul_le_mul_of_nonneg_left h₂ hc, mul_le_mul_of_nonneg_left h₃ hc,
    mul_le_mul_of_nonneg_left h₄ hc, mul_le_mul_of_nonneg_left h₅ hc,
    mul_le_mul_of_nonneg_left ht₁ hc, mul_le_mul_of_nonneg_left ht₂ hc,
    mul_le_mul_of_nonneg_left ht₃ hc, mul_le_mul_of_nonneg_left ht₄ hc]

/-- The same weighted bound holds for every testing radius L≤d. -/
theorem sourceOnePointMajorant_weight_of_le {ε L d M H Hv HU Hν N c : ℝ}
    (hL : 0 ≤ L) (hLd : L ≤ d) (hd : 0 < d) (hM : 0 < M)
    (hε : 0 ≤ ε) (hsmall : ε < 1 / 14)
    (hH : 0 ≤ H) (hHv : 0 ≤ Hv) (hHU : 0 ≤ HU) (hHν : 0 ≤ Hν)
    (hN : 0 ≤ N) (hc : 0 ≤ c) (hscale : d * M ≤ 1) :
    d ^ (3 / 2 - 5 * ε) * sourceOnePointMajorant ε L M H Hv HU Hν N c ≤
      M + c * (d ^ (1 - 2 * ε) * H + 3 * d ^ (1 / 2 - 3 * ε) * Hv +
        d ^ (3 / 2 - 5 * ε) * HU + d ^ (3 / 2 - 5 * ε) * Hν + d * N + 5 * M) := by
  exact (mul_le_mul_of_nonneg_left
    (sourceOnePointMajorant_mono hL hLd hε hsmall hM.le hH hHv hHU hHν hN hc)
    (Real.rpow_nonneg hd.le _)).trans
    (sourceOnePointMajorant_weight hd hM hsmall hH hHv hHU hHν hN hc hscale)

end GlobalPhi43.MW20
