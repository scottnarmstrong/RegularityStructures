/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.TreeI2Psi2DiagramAlg

/-!
# Elementary inequalities between powers of three scales, general exponents

Let `0 < r, r' ≤ 1` (the scales `s(y - x)`, `s(y' - x)`), `d > 0` with `d ≤ 8 (r + r')` (the scale
`s(y - y')`).  The inequalities of `TreeI2Psi2DiagramAlg` are generalised to a free
homogeneity loss `ℓ ∈ [0, 1/2]` and a free top power `p`:

* `alg_max_key`: `(max r r')^α d^(-β) ≤ d^(-p) (r^(p-ℓ) + r'^(p-ℓ)) + 4 d^(-ℓ)` for
  `0 ≤ β ≤ p`, `β - ℓ ≤ α`;
* `alg_pair_key`: the same for `r^g r'^g d^(-β)` with `β - ℓ ≤ 2 g`;
* `alg_pat`: the product of two single integrals, one with a loss `σ`, bounded by `136` times
  `d^(-2) (r^(2-ℓ) + r'^(2-ℓ)) + d^(-ℓ) + r^(-ℓ)`.
-/

public section

namespace RegularityStructures

theorem sixteen_rpow_le_four {ℓ : ℝ} (hℓ : ℓ ≤ 1 / 2) : (16 : ℝ) ^ ℓ ≤ 4 := by
  have h : (16 : ℝ) ^ (1 / 2 : ℝ) = 4 := by
    have e : (16 : ℝ) = 4 ^ (2 : ℝ) := by norm_num
    rw [e, ← Real.rpow_mul (by norm_num)]
    norm_num
  calc (16 : ℝ) ^ ℓ ≤ 16 ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hℓ
    _ = 4 := h

/-- `m^α d^(-β) ≤ d^(-p) m^(p-ℓ) + 4 d^(-ℓ)` when `d ≤ 16 m`. -/
theorem alg_key {m d α β p ℓ : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1) (hd : 0 < d)
    (hdm : d ≤ 16 * m) (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ 1 / 2) (hβ0 : 0 ≤ β) (hβp : β ≤ p)
    (hα : β - ℓ ≤ α) :
    m ^ α * d ^ (-β) ≤ d ^ (-p) * m ^ (p - ℓ) + 4 * d ^ (-ℓ) := by
  have h1 : m ^ α ≤ m ^ (β - ℓ) := Real.rpow_le_rpow_of_exponent_ge hm0 hm1 hα
  have hdn : 0 ≤ d ^ (-β) := Real.rpow_nonneg hd.le _
  have h2 : m ^ α * d ^ (-β) ≤ m ^ (-ℓ) * (m ^ β * d ^ (-β)) := by
    have e : m ^ (β - ℓ) = m ^ (-ℓ) * m ^ β := by
      rw [← Real.rpow_add hm0]; congr 1; ring
    calc m ^ α * d ^ (-β) ≤ m ^ (β - ℓ) * d ^ (-β) := mul_le_mul_of_nonneg_right h1 hdn
      _ = _ := by rw [e]; ring
  have hmb : m ^ β * d ^ (-β) = (m / d) ^ β := by
    rw [Real.div_rpow hm0.le hd.le, Real.rpow_neg hd.le]; ring
  rw [hmb] at h2
  refine h2.trans ?_
  have n1 : 0 ≤ d ^ (-p) * m ^ (p - ℓ) :=
    mul_nonneg (Real.rpow_nonneg hd.le _) (Real.rpow_nonneg hm0.le _)
  have n2 : 0 ≤ d ^ (-ℓ) := Real.rpow_nonneg hd.le _
  rcases le_total d m with hdm' | hmd
  · have hx : 1 ≤ m / d := by rw [le_div_iff₀ hd]; linarith
    have h3 : (m / d) ^ β ≤ (m / d) ^ p := Real.rpow_le_rpow_of_exponent_le hx hβp
    have h4 : (m / d) ^ p = m ^ p * d ^ (-p) := by
      rw [Real.div_rpow hm0.le hd.le, Real.rpow_neg hd.le]; ring
    have h5 : m ^ (-ℓ) * m ^ p = m ^ (p - ℓ) := by
      rw [← Real.rpow_add hm0]; congr 1; ring
    calc m ^ (-ℓ) * (m / d) ^ β ≤ m ^ (-ℓ) * (m ^ p * d ^ (-p)) := by
          rw [← h4]; exact mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hm0.le _)
      _ = d ^ (-p) * (m ^ (-ℓ) * m ^ p) := by ring
      _ = d ^ (-p) * m ^ (p - ℓ) := by rw [h5]
      _ ≤ _ := by linarith
  · have hx : m / d ≤ 1 := by rw [div_le_one hd]; exact hmd
    have h3 : (m / d) ^ β ≤ 1 := Real.rpow_le_one (div_nonneg hm0.le hd.le) hx hβ0
    have h4 : m ^ (-ℓ) ≤ (d / 16) ^ (-ℓ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (neg_nonpos.2 hℓ0)
    have h5 : (d / 16) ^ (-ℓ) = 16 ^ ℓ * d ^ (-ℓ) := by
      rw [Real.div_rpow hd.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 16),
        Real.rpow_neg hd.le]
      field_simp
    have h6 := sixteen_rpow_le_four hℓ
    calc m ^ (-ℓ) * (m / d) ^ β ≤ m ^ (-ℓ) * 1 :=
          mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hm0.le _)
      _ = m ^ (-ℓ) := mul_one _
      _ ≤ 16 ^ ℓ * d ^ (-ℓ) := h4.trans h5.le
      _ ≤ 4 * d ^ (-ℓ) := mul_le_mul_of_nonneg_right h6 n2
      _ ≤ _ := by linarith

/-- `max` version of `alg_key`, with the right-hand side in `r, r'`. -/
theorem alg_max_key {r r' d α β p ℓ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hr' : 0 < r')
    (hr1' : r' ≤ 1) (hd : 0 < d) (hdd : d ≤ 8 * (r + r')) (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ 1 / 2)
    (hβ0 : 0 ≤ β) (hβp : β ≤ p) (hα : β - ℓ ≤ α) :
    (max r r') ^ α * d ^ (-β) ≤
      d ^ (-p) * (r ^ (p - ℓ) + r' ^ (p - ℓ)) + 4 * d ^ (-ℓ) := by
  have hm0 : 0 < max r r' := lt_max_of_lt_left hr
  have hm1 : max r r' ≤ 1 := max_le hr1 hr1'
  have hdm : d ≤ 16 * max r r' := by
    have := le_max_left r r'
    have := le_max_right r r'
    linarith
  have h := alg_key hm0 hm1 hd hdm hℓ0 hℓ hβ0 hβp hα
  have h2 := max_rpow_le_add hr hr' (e := p - ℓ)
  have hn : 0 ≤ d ^ (-p) := Real.rpow_nonneg hd.le _
  have := mul_le_mul_of_nonneg_left h2 hn
  linarith

/-- `r^g r'^g d^(-β) ≤ d^(-p) (r^(p-ℓ) + r'^(p-ℓ)) + 4 d^(-ℓ)` when `β - ℓ ≤ 2 g`. -/
theorem alg_pair_key {r r' d g β p ℓ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hr' : 0 < r')
    (hr1' : r' ≤ 1) (hd : 0 < d) (hdd : d ≤ 8 * (r + r')) (hg : 0 ≤ g) (hℓ0 : 0 ≤ ℓ)
    (hℓ : ℓ ≤ 1 / 2) (hβ0 : 0 ≤ β) (hβp : β ≤ p) (hα : β - ℓ ≤ 2 * g) :
    r ^ g * r' ^ g * d ^ (-β) ≤ d ^ (-p) * (r ^ (p - ℓ) + r' ^ (p - ℓ)) + 4 * d ^ (-ℓ) := by
  have hXY := rpow_mul_rpow_le_max hr hr' (α := g) (α' := g) hg hg
  have e : g + g = 2 * g := by ring
  rw [e] at hXY
  have nD : 0 ≤ d ^ (-β) := Real.rpow_nonneg hd.le _
  exact (mul_le_mul_of_nonneg_right hXY nD).trans
    (alg_max_key hr hr1 hr' hr1' hd hdd hℓ0 hℓ hβ0 hβp hα)

/-- `r^g r'^g ≤ r^(2g) + r'^(2g)`. -/
theorem rpow_mul_rpow_le_add_two {r r' g : ℝ} (hr : 0 < r) (hr' : 0 < r') :
    r ^ g * r' ^ g ≤ r ^ (2 * g) + r' ^ (2 * g) := by
  have h1 : (r ^ g) ^ 2 = r ^ (2 * g) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]; congr 1; push_cast; ring
  have h2 : (r' ^ g) ^ 2 = r' ^ (2 * g) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr'.le]; congr 1; push_cast; ring
  nlinarith [sq_nonneg (r ^ g - r' ^ g), Real.rpow_nonneg hr.le g, Real.rpow_nonneg hr'.le g]

/-- For `d ≤ 16` and `0 ≤ σ ≤ ℓ ≤ σ + 1/2`: `d^(-σ) ≤ 4 d^(-ℓ)`. -/
theorem rpow_neg_le_four_mul {d σ ℓ : ℝ} (hd : 0 < d) (hd16 : d ≤ 16) (hσℓ : σ ≤ ℓ)
    (hℓσ : ℓ - σ ≤ 1 / 2) : d ^ (-σ) ≤ 4 * d ^ (-ℓ) := by
  have h1 : d ^ (ℓ - σ) ≤ 16 ^ (ℓ - σ) := Real.rpow_le_rpow hd.le hd16 (by linarith)
  have h2 := sixteen_rpow_le_four hℓσ
  have e : d ^ (-σ) = d ^ (-ℓ) * d ^ (ℓ - σ) := by
    rw [← Real.rpow_add hd]; congr 1; ring
  rw [e]
  have n : 0 ≤ d ^ (-ℓ) := Real.rpow_nonneg hd.le _
  nlinarith

/-- The product of two single integrals, one of them with a loss `σ`
(`d^(-σ) + r'^(-σ)`) and the other with gain `σ` on the other side. -/
theorem alg_pat {r r' d σ ℓ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hr' : 0 < r') (hr1' : r' ≤ 1)
    (hd : 0 < d) (hdd : d ≤ 8 * (r + r')) (hr'd : r' ≤ 16 * (r + d)) (hσ : 0 < σ)
    (hσ4 : σ ≤ 1 / 4) (hσℓ : σ ≤ ℓ) (hℓ : ℓ ≤ 1 / 2) :
    (d ^ (-σ) + r' ^ (-σ)) * (r' ^ σ * (d ^ (-σ) + r ^ (-σ))) ≤
      136 * (d ^ (-(2 : ℝ)) * (r ^ (2 - ℓ) + r' ^ (2 - ℓ)) + d ^ (-ℓ) + r ^ (-ℓ)) := by
  have hd16 : d ≤ 16 := by nlinarith
  have hr'a : r' ^ σ * r' ^ (-σ) = 1 := by rw [← Real.rpow_add hr']; simp
  have hra : r ^ σ * r ^ (-σ) = 1 := by rw [← Real.rpow_add hr]; simp
  have hda : d ^ σ * d ^ (-σ) = 1 := by rw [← Real.rpow_add hd]; simp
  have hdd2 : d ^ (-σ) * d ^ (-σ) = d ^ (-(2 * σ)) := by
    rw [← Real.rpow_add hd]; congr 1; ring
  have e : (d ^ (-σ) + r' ^ (-σ)) * (r' ^ σ * (d ^ (-σ) + r ^ (-σ))) =
      r' ^ σ * d ^ (-(2 * σ)) + r' ^ σ * d ^ (-σ) * r ^ (-σ) + d ^ (-σ) + r ^ (-σ) := by
    have : (d ^ (-σ) + r' ^ (-σ)) * (r' ^ σ * (d ^ (-σ) + r ^ (-σ))) =
        r' ^ σ * (d ^ (-σ) * d ^ (-σ)) + r' ^ σ * d ^ (-σ) * r ^ (-σ) +
          d ^ (-σ) * (r' ^ σ * r' ^ (-σ)) + r ^ (-σ) * (r' ^ σ * r' ^ (-σ)) := by ring
    rw [this, hdd2, hr'a]; ring
  rw [e]
  -- term (i)
  have t1 : r' ^ σ * d ^ (-(2 * σ)) ≤ d ^ (-(2 : ℝ)) * (r ^ (2 - ℓ) + r' ^ (2 - ℓ)) +
      4 * d ^ (-ℓ) := by
    have h := alg_max_key hr hr1 hr' hr1' hd hdd (α := σ) (β := 2 * σ) (p := 2) (ℓ := ℓ)
      (by linarith) hℓ (by linarith) (by linarith) (by linarith)
    have hm : r' ^ σ ≤ (max r r') ^ σ := Real.rpow_le_rpow hr'.le (le_max_right _ _) hσ.le
    have nD : 0 ≤ d ^ (-(2 * σ)) := Real.rpow_nonneg hd.le _
    exact (mul_le_mul_of_nonneg_right hm nD).trans h
  -- term (ii)
  have t2 : r' ^ σ * d ^ (-σ) * r ^ (-σ) ≤ 32 * (d ^ (-σ) + r ^ (-σ)) := by
    have hm : max r d ≤ 32 * max r d := by
      have : 0 ≤ max r d := le_max_of_le_left hr.le
      linarith
    have h1 : r' ≤ 32 * max r d := by
      have := le_max_left r d
      have := le_max_right r d
      linarith
    have h2 : r' ^ σ ≤ (32 * max r d) ^ σ := Real.rpow_le_rpow hr'.le h1 hσ.le
    rw [Real.mul_rpow (by norm_num) (le_max_of_le_left hr.le)] at h2
    have h32 : (32 : ℝ) ^ σ ≤ 32 := by
      calc (32 : ℝ) ^ σ ≤ 32 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 32 := Real.rpow_one 32
    have h3 : (max r d) ^ σ ≤ r ^ σ + d ^ σ := max_rpow_le_add hr hd
    have h4 : r' ^ σ ≤ 32 * (r ^ σ + d ^ σ) :=
      h2.trans (mul_le_mul h32 h3 (Real.rpow_nonneg (le_max_of_le_left hr.le) _) (by norm_num))
    have nn : 0 ≤ d ^ (-σ) * r ^ (-σ) :=
      mul_nonneg (Real.rpow_nonneg hd.le _) (Real.rpow_nonneg hr.le _)
    calc r' ^ σ * d ^ (-σ) * r ^ (-σ) = r' ^ σ * (d ^ (-σ) * r ^ (-σ)) := by ring
      _ ≤ 32 * (r ^ σ + d ^ σ) * (d ^ (-σ) * r ^ (-σ)) := mul_le_mul_of_nonneg_right h4 nn
      _ = 32 * ((r ^ σ * r ^ (-σ)) * d ^ (-σ) + (d ^ σ * d ^ (-σ)) * r ^ (-σ)) := by ring
      _ = _ := by rw [hra, hda]; ring
  have t3 : d ^ (-σ) ≤ 4 * d ^ (-ℓ) := rpow_neg_le_four_mul hd hd16 hσℓ (by linarith)
  have t4 : r ^ (-σ) ≤ r ^ (-ℓ) := Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)
  have nA : 0 ≤ d ^ (-(2 : ℝ)) * (r ^ (2 - ℓ) + r' ^ (2 - ℓ)) :=
    mul_nonneg (Real.rpow_nonneg hd.le _) (add_nonneg (Real.rpow_nonneg hr.le _)
      (Real.rpow_nonneg hr'.le _))
  have nB : 0 ≤ d ^ (-ℓ) := Real.rpow_nonneg hd.le _
  have nC : 0 ≤ r ^ (-ℓ) := Real.rpow_nonneg hr.le _
  linarith

end RegularityStructures

end
