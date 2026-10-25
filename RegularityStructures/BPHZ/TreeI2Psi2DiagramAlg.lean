/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Elementary inequalities between powers of three scales

Let `0 < r, r' ≤ 1` (the scales `s(y - x)`, `s(y' - x)`), `m = max r r'`, and `d > 0` with
`d ≤ 16 m` (the scale `s(y - y')`, by the quasi-triangle inequality).  We prove:

* `rpow_mul_rpow_le_key`: `m^α d^(-β) ≤ d^(-2) m^(2-δ) + 2 d^(-δ)` for `0 ≤ β ≤ 2`, `β - δ ≤ α`,
  `0 < δ ≤ 1/4`.  Every term of the chaos-`4` pairings is of this form.
-/

public section

namespace RegularityStructures

theorem sixteen_rpow_le_two {δ : ℝ} (hδ : δ ≤ 1 / 4) : (16 : ℝ) ^ δ ≤ 2 := by
  have h : (16 : ℝ) ^ (1 / 4 : ℝ) = 2 := by
    have e : (16 : ℝ) = 2 ^ (4 : ℝ) := by norm_num
    rw [e, ← Real.rpow_mul (by norm_num)]
    norm_num
  calc (16 : ℝ) ^ δ ≤ 16 ^ (1 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hδ
    _ = 2 := h

/-- Power comparison used for every term of the chaos-`4` pairings. -/
theorem rpow_mul_rpow_le_key {m d α β δ : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1) (hd : 0 < d)
    (hdm : d ≤ 16 * m) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 4) (hβ0 : 0 ≤ β) (hβ2 : β ≤ 2)
    (hα : β - δ ≤ α) :
    m ^ α * d ^ (-β) ≤ d ^ (-(2 : ℝ)) * m ^ (2 - δ) + 2 * d ^ (-δ) := by
  have h1 : m ^ α ≤ m ^ (β - δ) := Real.rpow_le_rpow_of_exponent_ge hm0 hm1 hα
  have hdn : 0 ≤ d ^ (-β) := Real.rpow_nonneg hd.le _
  have h2 : m ^ α * d ^ (-β) ≤ m ^ (-δ) * (m ^ β * d ^ (-β)) := by
    have e : m ^ (β - δ) = m ^ (-δ) * m ^ β := by
      rw [← Real.rpow_add hm0]; congr 1; ring
    calc m ^ α * d ^ (-β) ≤ m ^ (β - δ) * d ^ (-β) := mul_le_mul_of_nonneg_right h1 hdn
      _ = _ := by rw [e]; ring
  have hmb : m ^ β * d ^ (-β) = (m / d) ^ β := by
    rw [Real.div_rpow hm0.le hd.le, Real.rpow_neg hd.le]; ring
  rw [hmb] at h2
  refine h2.trans ?_
  have n1 : 0 ≤ d ^ (-(2 : ℝ)) * m ^ (2 - δ) :=
    mul_nonneg (Real.rpow_nonneg hd.le _) (Real.rpow_nonneg hm0.le _)
  have n2 : 0 ≤ d ^ (-δ) := Real.rpow_nonneg hd.le _
  rcases le_total d m with hdm' | hmd
  · have hx : 1 ≤ m / d := by rw [le_div_iff₀ hd]; linarith
    have h3 : (m / d) ^ β ≤ (m / d) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hβ2
    have h4 : (m / d) ^ (2 : ℝ) = m ^ (2 : ℝ) * d ^ (-(2 : ℝ)) := by
      rw [Real.div_rpow hm0.le hd.le, Real.rpow_neg hd.le]; ring
    have h5 : m ^ (-δ) * m ^ (2 : ℝ) = m ^ (2 - δ) := by
      rw [← Real.rpow_add hm0]; congr 1; ring
    calc m ^ (-δ) * (m / d) ^ β ≤ m ^ (-δ) * (m ^ (2 : ℝ) * d ^ (-(2 : ℝ))) := by
          rw [← h4]; exact mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hm0.le _)
      _ = d ^ (-(2 : ℝ)) * (m ^ (-δ) * m ^ (2 : ℝ)) := by ring
      _ = d ^ (-(2 : ℝ)) * m ^ (2 - δ) := by rw [h5]
      _ ≤ _ := by linarith
  · have hx : m / d ≤ 1 := by rw [div_le_one hd]; exact hmd
    have h3 : (m / d) ^ β ≤ 1 := Real.rpow_le_one (div_nonneg hm0.le hd.le) hx hβ0
    have h4 : m ^ (-δ) ≤ (d / 16) ^ (-δ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (neg_nonpos.2 hδ0)
    have h5 : (d / 16) ^ (-δ) = 16 ^ δ * d ^ (-δ) := by
      rw [Real.div_rpow hd.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 16),
        Real.rpow_neg hd.le]
      field_simp
    have h6 := sixteen_rpow_le_two hδ
    calc m ^ (-δ) * (m / d) ^ β ≤ m ^ (-δ) * 1 :=
          mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hm0.le _)
      _ = m ^ (-δ) := mul_one _
      _ ≤ 16 ^ δ * d ^ (-δ) := h4.trans h5.le
      _ ≤ 2 * d ^ (-δ) := mul_le_mul_of_nonneg_right h6 n2
      _ ≤ _ := by linarith

theorem rpow_mul_rpow_le_max {r r' α α' : ℝ} (hr : 0 < r) (hr' : 0 < r') (hα : 0 ≤ α)
    (hα' : 0 ≤ α') : r ^ α * r' ^ α' ≤ (max r r') ^ (α + α') := by
  rw [Real.rpow_add (lt_max_of_lt_left hr)]
  exact mul_le_mul (Real.rpow_le_rpow hr.le (le_max_left _ _) hα)
    (Real.rpow_le_rpow hr'.le (le_max_right _ _) hα') (Real.rpow_nonneg hr'.le _)
    (Real.rpow_nonneg (le_max_of_le_left hr.le) _)

theorem max_rpow_le_add {r r' e : ℝ} (hr : 0 < r) (hr' : 0 < r') :
    (max r r') ^ e ≤ r ^ e + r' ^ e := by
  have h1 := Real.rpow_nonneg hr.le e
  have h2 := Real.rpow_nonneg hr'.le e
  rcases le_total r r' with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; linarith

/-- `m = max r r'` version of `rpow_mul_rpow_le_key`, with the right-hand side in `r, r'`. -/
theorem max_rpow_mul_rpow_le {r r' d α β δ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hr' : 0 < r')
    (hr1' : r' ≤ 1) (hd : 0 < d) (hdd : d ≤ 8 * (r + r')) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 4)
    (hβ0 : 0 ≤ β) (hβ2 : β ≤ 2) (hα : β - δ ≤ α) :
    (max r r') ^ α * d ^ (-β) ≤
      d ^ (-(2 : ℝ)) * (r ^ (2 - δ) + r' ^ (2 - δ)) + 2 * d ^ (-δ) := by
  have hm0 : 0 < max r r' := lt_max_of_lt_left hr
  have hm1 : max r r' ≤ 1 := max_le hr1 hr1'
  have hdm : d ≤ 16 * max r r' := by
    have := le_max_left r r'
    have := le_max_right r r'
    linarith
  have h := rpow_mul_rpow_le_key hm0 hm1 hd hdm hδ0 hδ hβ0 hβ2 hα
  have h2 := max_rpow_le_add hr hr' (e := 2 - δ)
  have hn : 0 ≤ d ^ (-(2 : ℝ)) := Real.rpow_nonneg hd.le _
  have := mul_le_mul_of_nonneg_left h2 hn
  linarith

/-- The principal pairing of chaos `4`: `d^(-2) r^θ r'^θ ≲ d^(-2) (r^(2-δ) + r'^(2-δ))` for
`θ = 1 - δ/2`. -/
theorem rpow_mul_rpow_sq_le {r r' δ : ℝ} (hr : 0 < r) (hr' : 0 < r') :
    r ^ (1 - δ / 2) * r' ^ (1 - δ / 2) ≤ r ^ (2 - δ) + r' ^ (2 - δ) := by
  have h1 : (r ^ (1 - δ / 2)) ^ 2 = r ^ (2 - δ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]; congr 1; push_cast; ring
  have h2 : (r' ^ (1 - δ / 2)) ^ 2 = r' ^ (2 - δ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr'.le]; congr 1; push_cast; ring
  nlinarith [sq_nonneg (r ^ (1 - δ / 2) - r' ^ (1 - δ / 2))]

theorem one_le_two_mul_rpow {d δ : ℝ} (hd : 0 < d) (hd16 : d ≤ 16) (hδ : δ ≤ 1 / 4) (hδ0 : 0 ≤ δ) :
    1 ≤ 2 * d ^ (-δ) := by
  have h1 : (16 : ℝ) ^ (-δ) ≤ d ^ (-δ) := Real.rpow_le_rpow_of_nonpos hd hd16 (neg_nonpos.2 hδ0)
  have h2 := sixteen_rpow_le_two hδ
  have h3 : (16 : ℝ) ^ (-δ) * 16 ^ δ = 1 := by
    rw [← Real.rpow_add (by norm_num)]; simp
  have h4 : 0 ≤ (16 : ℝ) ^ (-δ) := Real.rpow_nonneg (by norm_num) _
  nlinarith

/-- The product pairing of chaos `4` (`θ = 1/2`): `E ≤ 8 (d^(-δ) + d^(-2) (r^(2-δ) + r'^(2-δ)))`. -/
theorem alg_chaos4_prod {r r' d δ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hr' : 0 < r') (hr1' : r' ≤ 1)
    (hd : 0 < d) (hdd : d ≤ 8 * (r + r')) (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) :
    r ^ (1 / 2 : ℝ) * r' ^ (1 / 2 : ℝ) * (d ^ (-(1 / 2 : ℝ)) + r' ^ (-(1 / 2 : ℝ))) *
        (d ^ (-(1 / 2 : ℝ)) + r ^ (-(1 / 2 : ℝ))) ≤
      8 * (d ^ (-δ) + d ^ (-(2 : ℝ)) * (r ^ (2 - δ) + r' ^ (2 - δ))) := by
  have k1 := max_rpow_mul_rpow_le hr hr1 hr' hr1' hd hdd hδ.le hδ4 (α := 1) (β := 1)
    zero_le_one (by norm_num) (by linarith)
  have k2 := max_rpow_mul_rpow_le hr hr1 hr' hr1' hd hdd hδ.le hδ4 (α := 1 / 2) (β := 1 / 2)
    (by norm_num) (by norm_num) (by linarith)
  have hX : r ^ (1 / 2 : ℝ) * r ^ (-(1 / 2 : ℝ)) = 1 := by
    rw [← Real.rpow_add hr]; simp
  have hY : r' ^ (1 / 2 : ℝ) * r' ^ (-(1 / 2 : ℝ)) = 1 := by
    rw [← Real.rpow_add hr']; simp
  have hDD : d ^ (-(1 / 2 : ℝ)) * d ^ (-(1 / 2 : ℝ)) = d ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_add hd]; norm_num
  have hXY := rpow_mul_rpow_le_max hr hr' (α := 1 / 2) (α' := 1 / 2) (by norm_num) (by norm_num)
  have hXm : r ^ (1 / 2 : ℝ) ≤ (max r r') ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow hr.le (le_max_left _ _) (by norm_num)
  have hYm : r' ^ (1 / 2 : ℝ) ≤ (max r r') ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow hr'.le (le_max_right _ _) (by norm_num)
  have e12 : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
  rw [e12] at hXY
  have nD : 0 ≤ d ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hd.le _
  have nD1 : 0 ≤ d ^ (-(1 : ℝ)) := Real.rpow_nonneg hd.le _
  have t1 : r ^ (1 / 2 : ℝ) * r' ^ (1 / 2 : ℝ) * d ^ (-(1 : ℝ)) ≤
      d ^ (-(2 : ℝ)) * (r ^ (2 - δ) + r' ^ (2 - δ)) + 2 * d ^ (-δ) := by
    refine le_trans (mul_le_mul_of_nonneg_right hXY nD1) k1
  have t2 : r' ^ (1 / 2 : ℝ) * d ^ (-(1 / 2 : ℝ)) ≤
      d ^ (-(2 : ℝ)) * (r ^ (2 - δ) + r' ^ (2 - δ)) + 2 * d ^ (-δ) :=
    le_trans (mul_le_mul_of_nonneg_right hYm nD) k2
  have t3 : r ^ (1 / 2 : ℝ) * d ^ (-(1 / 2 : ℝ)) ≤
      d ^ (-(2 : ℝ)) * (r ^ (2 - δ) + r' ^ (2 - δ)) + 2 * d ^ (-δ) :=
    le_trans (mul_le_mul_of_nonneg_right hXm nD) k2
  have hd16 : d ≤ 16 := by nlinarith
  have t4 := one_le_two_mul_rpow hd hd16 hδ4 hδ.le
  have hS : 0 ≤ d ^ (-(2 : ℝ)) * (r ^ (2 - δ) + r' ^ (2 - δ)) :=
    mul_nonneg (Real.rpow_nonneg hd.le _) (add_nonneg (Real.rpow_nonneg hr.le _)
      (Real.rpow_nonneg hr'.le _))
  have hE : r ^ (1 / 2 : ℝ) * r' ^ (1 / 2 : ℝ) * (d ^ (-(1 / 2 : ℝ)) + r' ^ (-(1 / 2 : ℝ))) *
        (d ^ (-(1 / 2 : ℝ)) + r ^ (-(1 / 2 : ℝ))) =
      r ^ (1 / 2 : ℝ) * r' ^ (1 / 2 : ℝ) * d ^ (-(1 : ℝ)) + r' ^ (1 / 2 : ℝ) * d ^ (-(1 / 2 : ℝ)) +
        r ^ (1 / 2 : ℝ) * d ^ (-(1 / 2 : ℝ)) + 1 := by
    have : r ^ (1 / 2 : ℝ) * r' ^ (1 / 2 : ℝ) * (d ^ (-(1 / 2 : ℝ)) + r' ^ (-(1 / 2 : ℝ))) *
        (d ^ (-(1 / 2 : ℝ)) + r ^ (-(1 / 2 : ℝ))) =
      r ^ (1 / 2 : ℝ) * r' ^ (1 / 2 : ℝ) * (d ^ (-(1 / 2 : ℝ)) * d ^ (-(1 / 2 : ℝ))) +
        r' ^ (1 / 2 : ℝ) * d ^ (-(1 / 2 : ℝ)) * (r ^ (1 / 2 : ℝ) * r ^ (-(1 / 2 : ℝ))) +
        r ^ (1 / 2 : ℝ) * d ^ (-(1 / 2 : ℝ)) * (r' ^ (1 / 2 : ℝ) * r' ^ (-(1 / 2 : ℝ))) +
        (r ^ (1 / 2 : ℝ) * r ^ (-(1 / 2 : ℝ))) * (r' ^ (1 / 2 : ℝ) * r' ^ (-(1 / 2 : ℝ))) := by ring
    rw [this, hDD, hX, hY]; ring
  rw [hE]
  linarith

/-- The cross pairing of chaos `4`: `d^(-1) r^a r'^a ≤ 2 (d^(-δ) + d^(-2) (r^(2-δ) + r'^(2-δ)))`
for `a = (1 - δ)/2`. -/
theorem alg_chaos4_cross {r r' d δ : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hr' : 0 < r') (hr1' : r' ≤ 1)
    (hd : 0 < d) (hdd : d ≤ 8 * (r + r')) (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) :
    d ^ (-(1 : ℝ)) * (r ^ ((1 - δ) / 2) * r' ^ ((1 - δ) / 2)) ≤
      2 * (d ^ (-δ) + d ^ (-(2 : ℝ)) * (r ^ (2 - δ) + r' ^ (2 - δ))) := by
  have k := max_rpow_mul_rpow_le hr hr1 hr' hr1' hd hdd hδ.le hδ4 (α := 1 - δ) (β := 1)
    zero_le_one (by norm_num) le_rfl
  have hXY := rpow_mul_rpow_le_max hr hr' (α := (1 - δ) / 2) (α' := (1 - δ) / 2)
    (by linarith) (by linarith)
  have e : (1 - δ) / 2 + (1 - δ) / 2 = 1 - δ := by ring
  rw [e] at hXY
  have nD1 : 0 ≤ d ^ (-(1 : ℝ)) := Real.rpow_nonneg hd.le _
  have := mul_le_mul_of_nonneg_left hXY nD1
  have n : 0 ≤ d ^ (-(2 : ℝ)) * (r ^ (2 - δ) + r' ^ (2 - δ)) :=
    mul_nonneg (Real.rpow_nonneg hd.le _) (add_nonneg (Real.rpow_nonneg hr.le _)
      (Real.rpow_nonneg hr'.le _))
  have n2 : 0 ≤ d ^ (-δ) := Real.rpow_nonneg hd.le _
  calc d ^ (-(1 : ℝ)) * (r ^ ((1 - δ) / 2) * r' ^ ((1 - δ) / 2))
      ≤ d ^ (-(1 : ℝ)) * (max r r') ^ (1 - δ) := this
    _ = (max r r') ^ (1 - δ) * d ^ (-(1 : ℝ)) := by ring
    _ ≤ _ := by linarith

theorem rpow_le_four_mul_of_le {d r' β : ℝ} (hr' : 0 < r') (hd : 0 < d) (hdd : d ≤ 16 * r')
    (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 2) : d ^ β ≤ 4 * r' ^ β := by
  have h1 : d ^ β ≤ (16 * r') ^ β := Real.rpow_le_rpow hd.le hdd hβ0
  rw [Real.mul_rpow (by norm_num) hr'.le] at h1
  have h2 : (16 : ℝ) ^ β ≤ 4 := by
    have e : (16 : ℝ) ^ (1 / 2 : ℝ) = 4 := by
      have e : (16 : ℝ) = 4 ^ (2 : ℝ) := by norm_num
      rw [e, ← Real.rpow_mul (by norm_num)]
      norm_num
    calc (16 : ℝ) ^ β ≤ 16 ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hβ
      _ = 4 := e
  exact h1.trans (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hr'.le _))

/-- The product pairing of chaos `2` in the regime `r ≤ r'`, with `θ = 1/2`, `ε' = 1/2 - a`:
`r^(1/2) (d^(-1/2) + r'^(-1/2)) (d^(-(1/2-a)) + r^(-(1/2-a))) ≤ 40 r^a r'^a d^(-1)`. -/
theorem alg_chaos2_prod {r r' d a : ℝ} (hr : 0 < r) (hrr : r ≤ r') (hr1' : r' ≤ 1) (hd : 0 < d)
    (hdd : d ≤ 16 * r') (ha : 0 < a) (ha2 : a < 1 / 2) :
    r ^ (1 / 2 : ℝ) * (d ^ (-(1 / 2 : ℝ)) + r' ^ (-(1 / 2 : ℝ))) *
        (d ^ (-(1 / 2 - a)) + r ^ (-(1 / 2 - a))) ≤
      40 * (r ^ a * r' ^ a * d ^ (-(1 : ℝ))) := by
  have hr' : 0 < r' := lt_of_lt_of_le hr hrr
  have nr : ∀ (u e : ℝ), 0 < u → 0 ≤ u ^ e := fun u e hu => Real.rpow_nonneg hu.le e
  -- `r'^(-1/2) ≤ 4 d^(-1/2)`
  have s1 : r' ^ (-(1 / 2 : ℝ)) ≤ 4 * d ^ (-(1 / 2 : ℝ)) := by
    have h : r' ^ (-(1 / 2 : ℝ)) ≤ (d / 16) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
    have e : (d / 16) ^ (-(1 / 2 : ℝ)) = 4 * d ^ (-(1 / 2 : ℝ)) := by
      rw [Real.div_rpow hd.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 16)]
      have e4 : (16 : ℝ) ^ (1 / 2 : ℝ) = 4 := by
        have e : (16 : ℝ) = 4 ^ (2 : ℝ) := by norm_num
        rw [e, ← Real.rpow_mul (by norm_num)]
        norm_num
      rw [e4]
      have : 0 < d ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hd _
      field_simp
    rwa [e] at h
  have nD : 0 ≤ d ^ (-(1 / 2 : ℝ)) := nr d _ hd
  have nD' : 0 ≤ d ^ (-(1 / 2 - a)) := nr d _ hd
  have nR' : 0 ≤ r ^ (-(1 / 2 - a)) := nr r _ hr
  have nX : 0 ≤ r ^ (1 / 2 : ℝ) := nr r _ hr
  have step1 : r ^ (1 / 2 : ℝ) * (d ^ (-(1 / 2 : ℝ)) + r' ^ (-(1 / 2 : ℝ))) *
        (d ^ (-(1 / 2 - a)) + r ^ (-(1 / 2 - a))) ≤
      5 * (r ^ (1 / 2 : ℝ) * d ^ (-(1 / 2 : ℝ)) * d ^ (-(1 / 2 - a)) +
        r ^ (1 / 2 : ℝ) * d ^ (-(1 / 2 : ℝ)) * r ^ (-(1 / 2 - a))) := by
    have h : r ^ (1 / 2 : ℝ) * (d ^ (-(1 / 2 : ℝ)) + r' ^ (-(1 / 2 : ℝ))) ≤
        r ^ (1 / 2 : ℝ) * (5 * d ^ (-(1 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left (by linarith) nX
    calc _ ≤ r ^ (1 / 2 : ℝ) * (5 * d ^ (-(1 / 2 : ℝ))) * (d ^ (-(1 / 2 - a)) + r ^ (-(1 / 2 - a))) :=
          mul_le_mul_of_nonneg_right h (add_nonneg nD' nR')
      _ = _ := by ring
  -- the two terms
  have hdb : ∀ β : ℝ, 0 ≤ β → β ≤ 1 / 2 → d ^ β ≤ 4 * r' ^ β := fun β h0 h1 =>
    rpow_le_four_mul_of_le hr' hd hdd h0 h1
  have hr'a : r' ^ (1 / 2 : ℝ) ≤ r' ^ a :=
    Real.rpow_le_rpow_of_exponent_ge hr' hr1' ha2.le
  have U1 : r ^ (1 / 2 : ℝ) * d ^ (-(1 / 2 : ℝ)) * d ^ (-(1 / 2 - a)) ≤
      4 * (r ^ a * r' ^ a * d ^ (-(1 : ℝ))) := by
    have e1 : r ^ (1 / 2 : ℝ) = r ^ a * r ^ (1 / 2 - a) := by
      rw [← Real.rpow_add hr]; congr 1; ring
    have e2 : d ^ (-(1 / 2 : ℝ)) * d ^ (-(1 / 2 - a)) = d ^ (-(1 : ℝ)) * d ^ a := by
      rw [← Real.rpow_add hd, ← Real.rpow_add hd]; congr 1; ring
    have h3 : r ^ (1 / 2 - a) ≤ r' ^ (1 / 2 - a) :=
      Real.rpow_le_rpow hr.le hrr (by linarith)
    have h4 := hdb a ha.le ha2.le
    have e3 : r' ^ (1 / 2 - a) * r' ^ a = r' ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add hr']; congr 1; ring
    have nD1 : 0 ≤ d ^ (-(1 : ℝ)) := nr d _ hd
    have nra : 0 ≤ r ^ a := nr r _ hr
    calc r ^ (1 / 2 : ℝ) * d ^ (-(1 / 2 : ℝ)) * d ^ (-(1 / 2 - a))
        = r ^ a * r ^ (1 / 2 - a) * (d ^ (-(1 : ℝ)) * d ^ a) := by rw [e1, mul_assoc, e2]
      _ ≤ r ^ a * r' ^ (1 / 2 - a) * (d ^ (-(1 : ℝ)) * (4 * r' ^ a)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left h3 nra) (mul_le_mul_of_nonneg_left h4 nD1)
            (mul_nonneg nD1 (nr d _ hd)) (mul_nonneg nra (nr r' _ hr'))
      _ = 4 * (r ^ a * d ^ (-(1 : ℝ)) * (r' ^ (1 / 2 - a) * r' ^ a)) := by ring
      _ = 4 * (r ^ a * d ^ (-(1 : ℝ)) * r' ^ (1 / 2 : ℝ)) := by rw [e3]
      _ ≤ 4 * (r ^ a * d ^ (-(1 : ℝ)) * r' ^ a) := by
          gcongr
      _ = _ := by ring
  have U2 : r ^ (1 / 2 : ℝ) * d ^ (-(1 / 2 : ℝ)) * r ^ (-(1 / 2 - a)) ≤
      4 * (r ^ a * r' ^ a * d ^ (-(1 : ℝ))) := by
    have e1 : r ^ (1 / 2 : ℝ) * r ^ (-(1 / 2 - a)) = r ^ a := by
      rw [← Real.rpow_add hr]; congr 1; ring
    have e2 : d ^ (-(1 / 2 : ℝ)) = d ^ (-(1 : ℝ)) * d ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add hd]; congr 1; ring
    have h4 := hdb (1 / 2) (by norm_num) le_rfl
    have nD1 : 0 ≤ d ^ (-(1 : ℝ)) := nr d _ hd
    have nra : 0 ≤ r ^ a := nr r _ hr
    calc r ^ (1 / 2 : ℝ) * d ^ (-(1 / 2 : ℝ)) * r ^ (-(1 / 2 - a))
        = (r ^ (1 / 2 : ℝ) * r ^ (-(1 / 2 - a))) * d ^ (-(1 / 2 : ℝ)) := by ring
      _ = r ^ a * (d ^ (-(1 : ℝ)) * d ^ (1 / 2 : ℝ)) := by rw [e1, e2]
      _ ≤ r ^ a * (d ^ (-(1 : ℝ)) * (4 * r' ^ (1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 nD1) nra
      _ ≤ r ^ a * (d ^ (-(1 : ℝ)) * (4 * r' ^ a)) := by gcongr
      _ = _ := by ring
  linarith

end RegularityStructures

end
