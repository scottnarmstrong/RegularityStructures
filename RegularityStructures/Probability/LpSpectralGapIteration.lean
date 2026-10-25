/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Probability.Moments.Variance

/-!
# The scalar iteration behind the `L^p` spectral gap

The iteration of [HS23, Remark 2.21 and (2.8)] closes a power moment estimate after applying the
variance gap to a centred power. This file records the elementary closure estimate separately.
Keeping it independent of the white-noise definitions makes the later cylindrical theorem small and
keeps all growth and integrability assumptions visible at its boundary.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace RegularityStructures

/-- A variance-power estimate closes after Hölder at the next even moment.

The numerical constant is deliberately explicit.  This is the only nonlinear scalar step used
by the `L^p` iteration: if `a` is the current centred `L^p` size, `b` the derivative size, and
`d` the lower-power contribution, then
`a^p ≤ d^p + q² a^(p-2) b²` implies `a ≤ 3 (d + q b)`.
-/
theorem lp_power_closure {q : ℕ} (hq : 2 ≤ q) {a b d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hineq : a ^ (2 * q) ≤ d ^ (2 * q) + (q : ℝ) ^ 2 * a ^ (2 * q - 2) * b ^ 2) :
    a ≤ 3 * (d + (q : ℝ) * b) := by
  by_contra hnot
  have hlt : 3 * (d + (q : ℝ) * b) < a := lt_of_not_ge hnot
  have ha_pos : 0 < a := by
    have hnonneg : 0 ≤ d + (q : ℝ) * b := by positivity
    nlinarith
  have hdlt : d < a / 3 := by
    have hqb : 0 ≤ (q : ℝ) * b := by positivity
    nlinarith
  have hqblt : (q : ℝ) * b < a / 3 := by
    have hd' : 0 ≤ d := hd
    nlinarith
  have hp_ge_two : 2 ≤ 2 * q := by omega
  have hpow_three : (9 : ℝ) ≤ 3 ^ (2 * q) := by
    calc
      (9 : ℝ) = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ (2 * q) := pow_le_pow_right₀ (by norm_num) hp_ge_two
  have hdpow : d ^ (2 * q) < a ^ (2 * q) / 9 := by
    have hpow : d ^ (2 * q) < (a / 3) ^ (2 * q) := by
      exact pow_lt_pow_left₀ hdlt (by positivity) (by omega)
    have hfrac : a ^ (2 * q) / 3 ^ (2 * q) ≤ a ^ (2 * q) / 9 := by
      apply (div_le_div_iff₀ (by positivity) (by norm_num)).2
      exact mul_le_mul_of_nonneg_left hpow_three (pow_nonneg ha (2 * q))
    calc
      d ^ (2 * q) < (a / 3) ^ (2 * q) := hpow
      _ = a ^ (2 * q) / 3 ^ (2 * q) := by rw [div_pow]
      _ ≤ a ^ (2 * q) / 9 := hfrac
  have hcross : (q : ℝ) ^ 2 * a ^ (2 * q - 2) * b ^ 2 < a ^ (2 * q) / 9 := by
    have hsq : ((q : ℝ) * b) ^ 2 < (a / 3) ^ 2 := by
      exact pow_lt_pow_left₀ hqblt (by positivity) (by norm_num)
    have hmul : a ^ (2 * q - 2) * ((q : ℝ) * b) ^ 2 <
        a ^ (2 * q - 2) * (a / 3) ^ 2 := by
      exact mul_lt_mul_of_pos_left hsq (pow_pos ha_pos _)
    calc
      (q : ℝ) ^ 2 * a ^ (2 * q - 2) * b ^ 2 =
          a ^ (2 * q - 2) * ((q : ℝ) * b) ^ 2 := by ring
      _ < a ^ (2 * q - 2) * (a / 3) ^ 2 := hmul
      _ = a ^ (2 * q) / 9 := by
        have hexp : 2 * q - 2 + 2 = 2 * q := by omega
        rw [div_pow, ← mul_div_assoc, ← pow_add]
        rw [hexp]
        norm_num
  have hapos_pow : 0 < a ^ (2 * q) := pow_pos ha_pos _
  nlinarith [hineq]

/-- One even-moment step, after the variance estimate and Hölder have been supplied.

`I` is the current `2q`-moment, `J` is the `q`-moment of the carré du champ, and `m` is the
lower-power mean.  The two hypotheses `hmean` and `hcross` are exactly the lower-power and
Hölder steps in the proof of Hairer--Steele (2.8). -/
theorem lp_power_step {q : ℕ} (hq : 2 ≤ q) {I J m cross D : ℝ}
    (hI : 0 ≤ I) (hJ : 0 ≤ J) (hD : 0 ≤ D)
    (hmean : m ^ 2 ≤ D ^ (2 * q) * J)
    (hvariance : I - m ^ 2 ≤ (q : ℝ) ^ 2 * cross)
    (hcross : cross ≤ I ^ ((q - 1 : ℝ) / q) * J ^ ((1 : ℝ) / q)) :
    I ^ (1 / (2 * q : ℝ)) ≤ 3 * (D + (q : ℝ)) * J ^ (1 / (2 * q : ℝ)) := by
  have hqpos : 0 < q := by omega
  let A : ℝ := I ^ (1 / (2 * q : ℝ))
  let B : ℝ := J ^ (1 / (2 * q : ℝ))
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact Real.rpow_nonneg hI _
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact Real.rpow_nonneg hJ _
  have hA_pow : A ^ (2 * q) = I := by
    dsimp [A]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hI]
    norm_num [Nat.cast_mul]
    have hexp : (q : ℝ)⁻¹ * (1 / 2) * (2 * (q : ℝ)) = 1 := by field_simp
    rw [hexp]
    exact Real.rpow_one I
  have hB_pow : B ^ (2 * q) = J := by
    dsimp [B]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hJ]
    norm_num [Nat.cast_mul]
    have hexp : (q : ℝ)⁻¹ * (1 / 2) * (2 * (q : ℝ)) = 1 := by field_simp
    rw [hexp]
    exact Real.rpow_one J
  have hDB_pow : (D * B) ^ (2 * q) = D ^ (2 * q) * J := by
    rw [mul_pow, hB_pow]
  have hcross' : cross ≤ A ^ (2 * q - 2) * B ^ 2 := by
    calc
      cross ≤ I ^ ((q - 1 : ℝ) / q) * J ^ ((1 : ℝ) / q) := hcross
      _ = A ^ (2 * q - 2) * B ^ 2 := by
        dsimp [A, B]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hI,
          ← Real.rpow_natCast, ← Real.rpow_mul hJ]
        have hqne : (q : ℝ) ≠ 0 := by positivity
        have hfirst : (1 / (2 * q : ℝ)) * ((2 * q - 2 : ℕ) : ℝ) =
            (q - 1 : ℝ) / q := by
          rw [Nat.cast_sub (by omega), Nat.cast_mul]
          field_simp; ring
        have hsecond : (1 / (2 * q : ℝ)) * ((2 : ℕ) : ℝ) = (1 : ℝ) / q := by
          field_simp; norm_num
        rw [hfirst, hsecond]
  have hIineq : I ≤ (D * B) ^ (2 * q) +
      (q : ℝ) ^ 2 * A ^ (2 * q - 2) * B ^ 2 := by
    have hcross_mul := mul_le_mul_of_nonneg_left hcross' (sq_nonneg (q : ℝ))
    calc
      I ≤ m ^ 2 + (q : ℝ) ^ 2 * cross := by linarith
      _ ≤ D ^ (2 * q) * J + (q : ℝ) ^ 2 * (A ^ (2 * q - 2) * B ^ 2) :=
        add_le_add hmean hcross_mul
      _ = (D * B) ^ (2 * q) + (q : ℝ) ^ 2 * A ^ (2 * q - 2) * B ^ 2 := by
        rw [hDB_pow]
        ring
  rw [← hA_pow] at hIineq
  have hcl := lp_power_closure hq hA_nonneg hB_nonneg
    (mul_nonneg hD hB_nonneg) hIineq
  dsimp [A, B] at hcl ⊢
  calc
    I ^ (1 / (2 * q : ℝ)) ≤ 3 * (D * J ^ (1 / (2 * q : ℝ)) +
        (q : ℝ) * J ^ (1 / (2 * q : ℝ))) := hcl
    _ = 3 * (D + (q : ℝ)) * J ^ (1 / (2 * q : ℝ)) := by ring

end RegularityStructures

end
