/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Real algebra for the global covariance bound of `I(Ψ³)Ψ²`

`i3Psi2_combine`: six term bounds, each dominated by a constant times
`(1 + D)² (1 + |z.1| + |z'.1|) Θ`, add up.
-/

public section

namespace RegularityStructures

theorem i3Psi2_combine {B Cp C0 CN1 CN2 Cc1 D U tz tz' Θ d1 dd a Se Sc T1 T2 T3 T4 T5 T6 : ℝ}
    (hB : 0 ≤ B) (hCp : 0 ≤ Cp) (hC0 : 0 ≤ C0) (hCN1 : 0 ≤ CN1) (hCN2 : 0 ≤ CN2)
    (hCc1 : 0 ≤ Cc1) (hD : 0 ≤ D) (hU : 0 ≤ U) (hUD : U ≤ 1 + D) (htz : 0 ≤ tz) (htz' : 0 ≤ tz')
    (hΘ : 0 ≤ Θ) (hd1 : 0 ≤ d1) (hdd : 0 ≤ dd) (ha : 0 ≤ a)
    (hdd' : dd ≤ Θ) (hq : d1 * a ≤ 6 * Θ) (hSe : Se ≤ 3 * Θ) (hSe0 : 0 ≤ Se) (hSc : Sc ≤ 6 * Θ)
    (hSc0 : 0 ≤ Sc)
    (h1 : |T1| ≤ 12 * (B ^ 2 * dd) * (Cp * (82 + 2 * tz)))
    (h2 : |T2| ≤ 72 * B * (C0 * U * (d1 * a)))
    (h3 : |T3| ≤ 36 * (CN1 * U * Se))
    (h4 : |T4| ≤ 72 * B * (C0 * U * (d1 * a)))
    (h5 : |T5| ≤ 144 * (CN2 * U * Se))
    (h6 : |T6| ≤ Cc1 * (1 + U) ^ 2 * Sc) :
    |T1 + T2 + T3 + T4 + T5 + T6| ≤
      (984 * B ^ 2 * Cp + 864 * B * C0 + 108 * CN1 + 432 * CN2 + 24 * Cc1) *
        ((1 + D) ^ 2 * (1 + tz + tz')) * Θ := by
  have hF1 : 1 ≤ (1 + D) ^ 2 := one_le_pow₀ (by linarith)
  have hF2 : 1 ≤ 1 + tz + tz' := by linarith
  have hUF : U ≤ (1 + D) ^ 2 := hUD.trans (le_self_pow₀ (by linarith) two_ne_zero)
  set Fac : ℝ := (1 + D) ^ 2 * (1 + tz + tz') with hFac
  have hFac0 : 0 ≤ Fac := by positivity
  have hUF' : U ≤ Fac := hUF.trans (le_mul_of_one_le_right (by positivity) hF2)
  have hF1' : 1 + tz ≤ Fac := by
    calc 1 + tz ≤ 1 + tz + tz' := by linarith
      _ = 1 * (1 + tz + tz') := by ring
      _ ≤ (1 + D) ^ 2 * (1 + tz + tz') := mul_le_mul_of_nonneg_right hF1 (by positivity)
  have hU1 : (1 + U) ^ 2 ≤ 4 * Fac := by
    have : (1 + U) ^ 2 ≤ (2 + D) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
    have h2' : (2 + D) ^ 2 ≤ 4 * (1 + D) ^ 2 := by linarith [sq_nonneg D]
    calc (1 + U) ^ 2 ≤ 4 * (1 + D) ^ 2 := this.trans h2'
      _ = 4 * ((1 + D) ^ 2 * 1) := by ring
      _ ≤ 4 * Fac := by
          have := mul_le_mul_of_nonneg_left hF2 (by positivity : (0 : ℝ) ≤ (1 + D) ^ 2)
          linarith
  have b1 : |T1| ≤ 984 * B ^ 2 * Cp * Fac * Θ := by
    have e : 12 * (B ^ 2 * dd) * (Cp * (82 + 2 * tz)) = (12 * B ^ 2 * Cp * dd) * (82 + 2 * tz) := by
      ring
    rw [e] at h1
    have hc : 0 ≤ 12 * B ^ 2 * Cp * dd := by positivity
    calc |T1| ≤ (12 * B ^ 2 * Cp * dd) * (82 + 2 * tz) := h1
      _ ≤ (12 * B ^ 2 * Cp * Θ) * (82 * Fac) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hdd' (by positivity)) ?_ (by positivity)
            (by positivity)
          linarith
      _ = _ := by ring
  have bc : 72 * B * (C0 * U * (d1 * a)) ≤ 432 * B * C0 * Fac * Θ := by
    have hc : 0 ≤ 72 * B * C0 := by positivity
    calc 72 * B * (C0 * U * (d1 * a)) = (72 * B * C0) * (U * (d1 * a)) := by ring
      _ ≤ (72 * B * C0) * (Fac * (6 * Θ)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul hUF' hq (mul_nonneg hd1 ha) hFac0) hc
      _ = _ := by ring
  have b3 : |T3| ≤ 108 * CN1 * Fac * Θ := by
    calc |T3| ≤ 36 * (CN1 * U * Se) := h3
      _ = (36 * CN1) * (U * Se) := by ring
      _ ≤ (36 * CN1) * (Fac * (3 * Θ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hUF' hSe hSe0 hFac0) (by positivity)
      _ = _ := by ring
  have b5 : |T5| ≤ 432 * CN2 * Fac * Θ := by
    calc |T5| ≤ 144 * (CN2 * U * Se) := h5
      _ = (144 * CN2) * (U * Se) := by ring
      _ ≤ (144 * CN2) * (Fac * (3 * Θ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hUF' hSe hSe0 hFac0) (by positivity)
      _ = _ := by ring
  have b6 : |T6| ≤ 24 * Cc1 * Fac * Θ := by
    calc |T6| ≤ Cc1 * (1 + U) ^ 2 * Sc := h6
      _ = Cc1 * ((1 + U) ^ 2 * Sc) := by ring
      _ ≤ Cc1 * ((4 * Fac) * (6 * Θ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hU1 hSc hSc0 (by positivity)) hCc1
      _ = _ := by ring
  have e1 := abs_add_le (T1 + T2 + T3 + T4 + T5) T6
  have e2 := abs_add_le (T1 + T2 + T3 + T4) T5
  have e3 := abs_add_le (T1 + T2 + T3) T4
  have e4 := abs_add_le (T1 + T2) T3
  have e5 := abs_add_le T1 T2
  have hfin : (984 * B ^ 2 * Cp + 864 * B * C0 + 108 * CN1 + 432 * CN2 + 24 * Cc1) * Fac * Θ =
      984 * B ^ 2 * Cp * Fac * Θ + 2 * (432 * B * C0 * Fac * Θ) + 108 * CN1 * Fac * Θ +
        432 * CN2 * Fac * Θ + 24 * Cc1 * Fac * Θ := by ring
  rw [hfin]
  linarith [e1, e2, e3, e4, e5, b1, b3, b5, b6, h2.trans bc, h4.trans bc]

end RegularityStructures

end
