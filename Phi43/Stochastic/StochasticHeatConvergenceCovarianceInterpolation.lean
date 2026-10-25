/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Interpolation of two covariance bounds

The covariance estimates for the heat-field increments have a singular bound and a translation
bound.  This file contains the elementary interpolation step which turns the two bounds into the
fractional estimate used by the heat-pair integrals.  It is kept independent of the stochastic
definitions so that the analytic kernel estimates can use it without importing the Gaussian layer.
-/

@[expose] public noncomputable section

open Real

namespace RegularityStructures.Phi43

private theorem le_rpow_mul_rpow_of_le {a b : ℝ} {θ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hθ : 0 ≤ θ) (_hθ1 : θ ≤ 1)
    (hab : a ≤ b) :
    a ≤ a ^ (1 - θ) * b ^ θ := by
  by_cases ha0 : a = 0
  · subst a
    positivity
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hpow : a ^ (1 - θ) * a ^ θ = a := by
    rw [← Real.rpow_add ha']
    simp
  calc
    a = a ^ (1 - θ) * a ^ θ := hpow.symm
    _ ≤ a ^ (1 - θ) * b ^ θ := by
      gcongr

private theorem le_rpow_mul_rpow_of_ge {a b : ℝ} {θ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (_hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hba : b ≤ a) :
    b ≤ a ^ (1 - θ) * b ^ θ := by
  by_cases hb0 : b = 0
  · subst b
    positivity
  have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have hpow : b ^ (1 - θ) * b ^ θ = b := by
    rw [← Real.rpow_add hb']
    simp
  calc
    b = b ^ (1 - θ) * b ^ θ := hpow.symm
    _ ≤ a ^ (1 - θ) * b ^ θ := by
      gcongr

theorem le_rpow_interpolation {a A B θ : ℝ}
    (_ha : 0 ≤ a) (hA : 0 ≤ A) (hB : 0 ≤ B) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (haA : a ≤ A) (haB : a ≤ B) :
    a ≤ A ^ (1 - θ) * B ^ θ := by
  by_cases hAB : A ≤ B
  · exact haA.trans (le_rpow_mul_rpow_of_le hA hB hθ hθ1 hAB)
  · have hBA : B ≤ A := le_of_not_ge hAB
    exact haB.trans (le_rpow_mul_rpow_of_ge hA hB hθ hθ1 hBA)

theorem abs_le_interpolated_of_abs_le_of_abs_le {x A B d r θ : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hd : 0 ≤ d) (hr : 0 < r)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hxA : |x| ≤ A * r ^ (-(1 : ℝ)))
    (hxB : |x| ≤ B * d * r ^ (-(3 : ℝ))) :
    |x| ≤ A ^ (1 - θ) * B ^ θ * d ^ θ * r ^ (-(1 + 2 * θ : ℝ)) := by
  have hrpow : 0 < r ^ (1 : ℝ) := Real.rpow_pos_of_pos hr _
  have hri : 0 ≤ r ^ (-(1 : ℝ)) := Real.rpow_nonneg hr.le _
  have hri3 : 0 ≤ r ^ (-(3 : ℝ)) := Real.rpow_nonneg hr.le _
  have hA0 : 0 ≤ A * r ^ (-(1 : ℝ)) := mul_nonneg hA hri
  have hB0 : 0 ≤ B * d * r ^ (-(3 : ℝ)) :=
    mul_nonneg (mul_nonneg hB hd) hri3
  have hinterp := le_rpow_interpolation (a := |x|)
    (abs_nonneg x) hA0 hB0 hθ hθ1 hxA hxB
  have hfactor :
      (A * r ^ (-(1 : ℝ))) ^ (1 - θ) *
        (B * d * r ^ (-(3 : ℝ))) ^ θ =
      A ^ (1 - θ) * B ^ θ * d ^ θ * r ^ (-(1 + 2 * θ : ℝ)) := by
    rw [Real.mul_rpow hA hri, Real.mul_rpow (mul_nonneg hB hd) hri3]
    rw [Real.mul_rpow hB hd]
    rw [← Real.rpow_mul hr.le, ← Real.rpow_mul hr.le]
    have hrcombine :
        r ^ (-(1 : ℝ) * (1 - θ)) * r ^ (-(3 : ℝ) * θ) =
          r ^ (-(1 + 2 * θ : ℝ)) := by
      rw [← Real.rpow_add hr]
      congr 1
      ring
    calc
      A ^ (1 - θ) * r ^ (-(1 : ℝ) * (1 - θ)) *
          (B ^ θ * d ^ θ * r ^ (-(3 : ℝ) * θ)) =
          A ^ (1 - θ) * B ^ θ * d ^ θ *
            (r ^ (-(1 : ℝ) * (1 - θ)) * r ^ (-(3 : ℝ) * θ)) := by ring
      _ = A ^ (1 - θ) * B ^ θ * d ^ θ *
            r ^ (-(1 + 2 * θ : ℝ)) := by rw [hrcombine]
  rw [hfactor] at hinterp
  exact hinterp

end RegularityStructures.Phi43

end
