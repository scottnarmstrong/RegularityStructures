/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Elementary inequalities for the global covariance bound of `I(Ψ²) Ψ²`

Real-number inequalities used to combine the bounds of the single integrals: a product of two
sums `(p₁ + p₄)(p₂ + p₃)` with `p₂ ≤ 2 p₁` is at most `4 (p₁² + p₃² + p₄²)`, and `D^(1/4) ≤ 1 + D`.
-/

public section

namespace RegularityStructures

theorem prod_sum_le_four_sq {p₁ p₂ p₃ p₄ : ℝ} (h1 : 0 ≤ p₁) (h4 : 0 ≤ p₄) (hp : p₂ ≤ 2 * p₁) :
    (p₁ + p₄) * (p₂ + p₃) ≤ 4 * (p₁ ^ 2 + p₃ ^ 2 + p₄ ^ 2) := by
  have a : (p₁ + p₄) * (p₂ + p₃) ≤ (p₁ + p₄) * (2 * p₁ + p₃) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  nlinarith [sq_nonneg (p₁ - p₃), sq_nonneg (p₁ - p₄), sq_nonneg (p₃ - p₄), sq_nonneg p₁,
    sq_nonneg p₃, sq_nonneg p₄]

theorem rpow_quarter_le_one_add {D : ℝ} (hD : 0 ≤ D) : D ^ (1 / 4 : ℝ) ≤ 1 + D := by
  rcases le_total D 1 with h | h
  · have := Real.rpow_le_one hD h (by norm_num : (0 : ℝ) ≤ 1 / 4)
    linarith
  · have : D ^ (1 / 4 : ℝ) ≤ D ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h (by norm_num)
    rw [Real.rpow_one] at this
    linarith

theorem rpow_neg_quarter_sq {s : ℝ} (hs : 0 ≤ s) :
    (s ^ (-(1 / 4 : ℝ))) ^ 2 = s ^ (-(1 / 2 : ℝ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
  norm_num

end RegularityStructures

end

public section

namespace RegularityStructures

/-- Combination of the six bounds for the covariance of `I(Ψ²) Ψ²`: pure real algebra. -/
theorem i2Psi2_combine {B Csq Ccr Cch Cs2 Cs11 Cm a0 a1 D U t t' d1 d2 p1 p2 p3 p4 T1 T2 T3 T4 T5 T6 : ℝ}
    (hB : 0 ≤ B) (hCsq : 0 ≤ Csq) (hCcr : 0 ≤ Ccr) (hCch : 0 ≤ Cch) (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (hD : 0 ≤ D) (hU : 0 ≤ U)
    (hUD : U ≤ 1 + D) (ht : 0 ≤ t) (ht' : 0 ≤ t') (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2) (hp1 : 0 ≤ p1)
    (hp2 : p2 ≤ 2 * p1) (hp2' : 0 ≤ p2) (hp3 : 0 ≤ p3) (hp4 : 0 ≤ p4)
    (h1 : |T1| ≤ 4 * (B ^ 2 * d2) * (Csq * B ^ 4 * U * (a0 + 2 * (t + 1))))
    (h2 : |T2| ≤ 4 * ((Cs2 * B * (4 * B ^ 2) * U * (p1 + p4)) * (Cs2 * B * B ^ 2 * U * (p2 + p3))))
    (h3 : |T3| ≤ 16 * (B * d1) * (Ccr * B ^ 5 * U * (a1 + 2 * (t + 1))))
    (h4 : |T4| ≤ 16 * (B * d1) * (Cch * B ^ 5 * U * (a1 + 2 * (t + 1))))
    (h5 : |T5| ≤ 16 * ((Cs11 * B * (4 * B ^ 2) * U * (p1 + p4)) *
      (Cs11 * B * (2 * B ^ 2) * U * (p2 + p3))))
    (h6 : |T6| ≤ (Cm * B ^ 3 * U * p3) * (Cm * B ^ 3 * U * p4)) :
    |T1 + T2 + T3 + T4 + T5 + T6| ≤
      (4 * Csq * B ^ 6 * (a0 + 2) + 64 * Cs2 ^ 2 * B ^ 6 + 16 * Ccr * B ^ 6 * (a1 + 2) +
        16 * Cch * B ^ 6 * (a1 + 2) + 512 * Cs11 ^ 2 * B ^ 6 + Cm ^ 2 * B ^ 6) *
      ((1 + D) ^ 2 * (1 + t + t')) * (d2 + d1 + p1 ^ 2 + p3 ^ 2 + p4 ^ 2) := by
  have hF1 : 1 ≤ (1 + D) ^ 2 := one_le_pow₀ (by linarith)
  have hF2 : 1 ≤ 1 + t + t' := by linarith
  have hFac0 : 0 ≤ (1 + D) ^ 2 * (1 + t + t') := by positivity
  have hUF : U ≤ (1 + D) ^ 2 := hUD.trans (le_self_pow₀ (by linarith) two_ne_zero)
  have hU2 : U ^ 2 ≤ (1 + D) ^ 2 := pow_le_pow_left₀ hU hUD 2
  have hB6 : 0 ≤ B ^ 6 := pow_nonneg hB 6
  set Fac : ℝ := (1 + D) ^ 2 * (1 + t + t') with hFac
  set Sum : ℝ := d2 + d1 + p1 ^ 2 + p3 ^ 2 + p4 ^ 2 with hSum
  have s1 : d2 ≤ Sum := by
    have := sq_nonneg p1; have := sq_nonneg p3; have := sq_nonneg p4; linarith
  have s2 : d1 ≤ Sum := by
    have := sq_nonneg p1; have := sq_nonneg p3; have := sq_nonneg p4; linarith
  have s3 : p1 ^ 2 + p3 ^ 2 + p4 ^ 2 ≤ Sum := by linarith
  have s4 : p3 ^ 2 + p4 ^ 2 ≤ Sum := by
    have := sq_nonneg p1; linarith
  -- the factor `U (a + 2 (t + 1)) ≤ (a + 2) Fac`
  have hfac : ∀ a : ℝ, 0 ≤ a → U * (a + 2 * (t + 1)) ≤ (a + 2) * Fac := by
    intro a ha
    have h1' : a + 2 * (t + 1) ≤ (a + 2) * (1 + t + t') := by
      linarith only [mul_nonneg ha ht, mul_nonneg ha ht', ht']
    calc U * (a + 2 * (t + 1)) ≤ (1 + D) ^ 2 * ((a + 2) * (1 + t + t')) :=
          mul_le_mul hUF h1' (by positivity) (by positivity)
      _ = (a + 2) * Fac := by rw [hFac]; ring
  have b1 : |T1| ≤ 4 * Csq * B ^ 6 * (a0 + 2) * Fac * Sum := by
    have e : 4 * (B ^ 2 * d2) * (Csq * B ^ 4 * U * (a0 + 2 * (t + 1))) =
        (4 * Csq * B ^ 6 * d2) * (U * (a0 + 2 * (t + 1))) := by ring
    rw [e] at h1
    have hc : 0 ≤ 4 * Csq * B ^ 6 * d2 := by positivity
    calc |T1| ≤ (4 * Csq * B ^ 6 * d2) * (U * (a0 + 2 * (t + 1))) := h1
      _ ≤ (4 * Csq * B ^ 6 * d2) * ((a0 + 2) * Fac) :=
          mul_le_mul_of_nonneg_left (hfac a0 ha0) hc
      _ = (4 * Csq * B ^ 6 * (a0 + 2) * Fac) * d2 := by ring
      _ ≤ (4 * Csq * B ^ 6 * (a0 + 2) * Fac) * Sum :=
          mul_le_mul_of_nonneg_left s1 (by positivity)
  have b3 : |T3| ≤ 16 * Ccr * B ^ 6 * (a1 + 2) * Fac * Sum := by
    have e : 16 * (B * d1) * (Ccr * B ^ 5 * U * (a1 + 2 * (t + 1))) =
        (16 * Ccr * B ^ 6 * d1) * (U * (a1 + 2 * (t + 1))) := by ring
    rw [e] at h3
    have hc : 0 ≤ 16 * Ccr * B ^ 6 * d1 := by positivity
    calc |T3| ≤ (16 * Ccr * B ^ 6 * d1) * (U * (a1 + 2 * (t + 1))) := h3
      _ ≤ (16 * Ccr * B ^ 6 * d1) * ((a1 + 2) * Fac) :=
          mul_le_mul_of_nonneg_left (hfac a1 ha1) hc
      _ = (16 * Ccr * B ^ 6 * (a1 + 2) * Fac) * d1 := by ring
      _ ≤ (16 * Ccr * B ^ 6 * (a1 + 2) * Fac) * Sum :=
          mul_le_mul_of_nonneg_left s2 (by positivity)
  have b4 : |T4| ≤ 16 * Cch * B ^ 6 * (a1 + 2) * Fac * Sum := by
    have e : 16 * (B * d1) * (Cch * B ^ 5 * U * (a1 + 2 * (t + 1))) =
        (16 * Cch * B ^ 6 * d1) * (U * (a1 + 2 * (t + 1))) := by ring
    rw [e] at h4
    have hc : 0 ≤ 16 * Cch * B ^ 6 * d1 := by positivity
    calc |T4| ≤ (16 * Cch * B ^ 6 * d1) * (U * (a1 + 2 * (t + 1))) := h4
      _ ≤ (16 * Cch * B ^ 6 * d1) * ((a1 + 2) * Fac) :=
          mul_le_mul_of_nonneg_left (hfac a1 ha1) hc
      _ = (16 * Cch * B ^ 6 * (a1 + 2) * Fac) * d1 := by ring
      _ ≤ (16 * Cch * B ^ 6 * (a1 + 2) * Fac) * Sum :=
          mul_le_mul_of_nonneg_left s2 (by positivity)
  have hps := prod_sum_le_four_sq hp1 hp4 hp2 (p₃ := p3)
  have hUF2 : U ^ 2 ≤ Fac := by
    calc U ^ 2 ≤ (1 + D) ^ 2 := hU2
      _ = (1 + D) ^ 2 * 1 := by ring
      _ ≤ Fac := mul_le_mul_of_nonneg_left hF2 (by positivity)
  have hprod0 : 0 ≤ (p1 + p4) * (p2 + p3) :=
    mul_nonneg (add_nonneg hp1 hp4) (add_nonneg hp2' hp3)
  have key : ∀ c : ℝ, 0 ≤ c → c * (U ^ 2 * ((p1 + p4) * (p2 + p3))) ≤ 4 * c * Fac * Sum := by
    intro c hc
    calc c * (U ^ 2 * ((p1 + p4) * (p2 + p3)))
        ≤ c * (Fac * (4 * (p1 ^ 2 + p3 ^ 2 + p4 ^ 2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hUF2 hps hprod0 hFac0) hc
      _ ≤ c * (Fac * (4 * Sum)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hFac0) hc
          linarith
      _ = 4 * c * Fac * Sum := by ring
  have b2 : |T2| ≤ 64 * Cs2 ^ 2 * B ^ 6 * Fac * Sum := by
    have e : 4 * ((Cs2 * B * (4 * B ^ 2) * U * (p1 + p4)) * (Cs2 * B * B ^ 2 * U * (p2 + p3))) =
        (16 * Cs2 ^ 2 * B ^ 6) * (U ^ 2 * ((p1 + p4) * (p2 + p3))) := by ring
    rw [e] at h2
    refine h2.trans ((key _ (by positivity)).trans (le_of_eq (by ring)))
  have b5 : |T5| ≤ 512 * Cs11 ^ 2 * B ^ 6 * Fac * Sum := by
    have e : 16 * ((Cs11 * B * (4 * B ^ 2) * U * (p1 + p4)) *
        (Cs11 * B * (2 * B ^ 2) * U * (p2 + p3))) =
        (128 * Cs11 ^ 2 * B ^ 6) * (U ^ 2 * ((p1 + p4) * (p2 + p3))) := by ring
    rw [e] at h5
    refine h5.trans ((key _ (by positivity)).trans (le_of_eq (by ring)))
  have b6 : |T6| ≤ Cm ^ 2 * B ^ 6 * Fac * Sum := by
    have e : (Cm * B ^ 3 * U * p3) * (Cm * B ^ 3 * U * p4) =
        (Cm ^ 2 * B ^ 6) * (U ^ 2 * (p3 * p4)) := by ring
    rw [e] at h6
    have hpp : p3 * p4 ≤ Sum := by
      have := two_mul_le_add_sq p3 p4
      have := mul_nonneg hp3 hp4
      linarith
    calc |T6| ≤ (Cm ^ 2 * B ^ 6) * (U ^ 2 * (p3 * p4)) := h6
      _ ≤ (Cm ^ 2 * B ^ 6) * (Fac * Sum) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul hUF2 hpp (mul_nonneg hp3 hp4) hFac0
      _ = _ := by ring
  have e1 := abs_add_le (T1 + T2 + T3 + T4 + T5) T6
  have e2 := abs_add_le (T1 + T2 + T3 + T4) T5
  have e3 := abs_add_le (T1 + T2 + T3) T4
  have e4 := abs_add_le (T1 + T2) T3
  have e5 := abs_add_le T1 T2
  have hfin : (4 * Csq * B ^ 6 * (a0 + 2) + 64 * Cs2 ^ 2 * B ^ 6 + 16 * Ccr * B ^ 6 * (a1 + 2) +
        16 * Cch * B ^ 6 * (a1 + 2) + 512 * Cs11 ^ 2 * B ^ 6 + Cm ^ 2 * B ^ 6) * Fac * Sum =
      4 * Csq * B ^ 6 * (a0 + 2) * Fac * Sum + 64 * Cs2 ^ 2 * B ^ 6 * Fac * Sum +
      16 * Ccr * B ^ 6 * (a1 + 2) * Fac * Sum + 16 * Cch * B ^ 6 * (a1 + 2) * Fac * Sum +
      512 * Cs11 ^ 2 * B ^ 6 * Fac * Sum + Cm ^ 2 * B ^ 6 * Fac * Sum := by ring
  rw [hfin]
  linarith [e1, e2, e3, e4, e5, b1, b2, b3, b4, b5, b6]

/-- The polynomial prefactor in terms of the sizes: with `D = √(2 (t + t' + 2)) + 1`,
`(1 + D)² (1 + t + t') ≤ 125 (1 + a + b)³` if `t ≤ a`, `t' ≤ b`. -/
theorem poly_prefactor_le {t t' a b : ℝ} (ht : 0 ≤ t) (ht' : 0 ≤ t') (hta : t ≤ a)
    (htb : t' ≤ b) :
    (1 + (√(2 * (t + t' + 2)) + 1)) ^ 2 * (1 + t + t') ≤ 125 * (1 + a + b) ^ 3 := by
  have hR : 0 ≤ 2 * (t + t' + 2) := by positivity
  have hs0 : 0 ≤ √(2 * (t + t' + 2)) := Real.sqrt_nonneg _
  have hsq : √(2 * (t + t' + 2)) ≤ (1 + 2 * (t + t' + 2)) / 2 := by
    nlinarith [Real.sq_sqrt hR, sq_nonneg (√(2 * (t + t' + 2)) - 1)]
  have h1 : 1 + (√(2 * (t + t' + 2)) + 1) ≤ 5 * (1 + a + b) := by linarith
  have h1' : 0 ≤ 1 + (√(2 * (t + t' + 2)) + 1) := by linarith
  have h2 : 1 + t + t' ≤ 5 * (1 + a + b) := by linarith
  have h2' : 0 ≤ 1 + t + t' := by linarith
  calc (1 + (√(2 * (t + t' + 2)) + 1)) ^ 2 * (1 + t + t')
      ≤ (5 * (1 + a + b)) ^ 2 * (5 * (1 + a + b)) :=
        mul_le_mul (pow_le_pow_left₀ h1' h1 2) h2 h2' (by positivity)
    _ = 125 * (1 + a + b) ^ 3 := by ring

end RegularityStructures

end
