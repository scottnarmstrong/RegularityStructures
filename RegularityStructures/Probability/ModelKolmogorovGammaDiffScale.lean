/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

import Mathlib.Tactic.Linarith
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import RegularityStructures.Probability.KolmogorovChentsovScale

/-!
# Reserve bookkeeping for the two-model Gamma induction

The two possible mixed Chen channels put the stochastic reserve on either the coarse factor or the
fine factor. These elementary inequalities move the reserve to the coarse annulus while retaining a
positive fine-scale tail. They are the scale-algebra part of the Kolmogorov criterion for models.
-/

@[expose] public section

open scoped ENNReal NNReal

namespace RegularityStructures

theorem gammaDiffOfRealProductScale_le
    {C A B d e a b : ℝ} {q N l : ℕ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hd : 0 ≤ d) (he : 0 ≤ e) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hdle : d ≤ A * (1 / (2 : ℝ) ^ N))
    (hele : e ≤ B * (1 / (2 : ℝ) ^ (N + l))) :
    ENNReal.ofReal (C * d ^ a * e ^ b) ^ q ≤
      ENNReal.ofReal (C * A ^ a * B ^ b) ^ q *
        dyadicBase N ^ ((q : ℝ) * (a + b)) *
        dyadicBase l ^ ((q : ℝ) * b) := by
  have hd0 : 0 ≤ (1 / (2 : ℝ) ^ N) := by positivity
  have he0 : 0 ≤ (1 / (2 : ℝ) ^ (N + l)) := by positivity
  have hda : d ^ a ≤ (A * (1 / (2 : ℝ) ^ N)) ^ a :=
    Real.rpow_le_rpow hd hdle ha
  have heb : e ^ b ≤ (B * (1 / (2 : ℝ) ^ (N + l))) ^ b :=
    Real.rpow_le_rpow he hele hb
  have hprod : C * d ^ a * e ^ b ≤
      C * (A * (1 / (2 : ℝ) ^ N)) ^ a *
        (B * (1 / (2 : ℝ) ^ (N + l))) ^ b := by
    calc
      C * d ^ a * e ^ b ≤
          C * (A * (1 / (2 : ℝ) ^ N)) ^ a * e ^ b := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hda hC)
          (Real.rpow_nonneg he b)
      _ ≤ C * (A * (1 / (2 : ℝ) ^ N)) ^ a *
          (B * (1 / (2 : ℝ) ^ (N + l))) ^ b := by
        exact mul_le_mul_of_nonneg_left heb (by positivity)
  have hmain : ENNReal.ofReal (C * d ^ a * e ^ b) ^ q ≤
      ENNReal.ofReal (C * (A * (1 / (2 : ℝ) ^ N)) ^ a *
        (B * (1 / (2 : ℝ) ^ (N + l))) ^ b) ^ q :=
    ENNReal.pow_le_pow_left (ENNReal.ofReal_le_ofReal hprod)
  have hrewrite :
      ENNReal.ofReal (C * (A * (1 / (2 : ℝ) ^ N)) ^ a *
        (B * (1 / (2 : ℝ) ^ (N + l))) ^ b) ^ q =
      ENNReal.ofReal (C * A ^ a * B ^ b) ^ q *
        dyadicBase N ^ ((q : ℝ) * (a + b)) *
        dyadicBase l ^ ((q : ℝ) * b) := by
    rw [Real.mul_rpow hA hd0, Real.mul_rpow hB he0]
    have hreal : C * (A ^ a * (1 / (2 : ℝ) ^ N) ^ a) *
        (B ^ b * (1 / (2 : ℝ) ^ (N + l)) ^ b) =
        (C * A ^ a * B ^ b) *
          (1 / (2 : ℝ) ^ N) ^ (a + b) *
          (1 / (2 : ℝ) ^ l) ^ b := by
      rw [show (1 / (2 : ℝ) ^ (N + l)) =
          (1 / (2 : ℝ) ^ N) * (1 / (2 : ℝ) ^ l) by
        rw [pow_add]
        ring]
      rw [Real.mul_rpow (by positivity) (by positivity)]
      calc
        C * (A ^ a * (1 / (2 : ℝ) ^ N) ^ a) *
            (B ^ b * ((1 / (2 : ℝ) ^ N) ^ b *
              (1 / (2 : ℝ) ^ l) ^ b)) =
            C * A ^ a * B ^ b *
              ((1 / (2 : ℝ) ^ N) ^ a *
                (1 / (2 : ℝ) ^ N) ^ b) *
              (1 / (2 : ℝ) ^ l) ^ b := by ring
        _ = (C * A ^ a * B ^ b) *
              (1 / (2 : ℝ) ^ N) ^ (a + b) *
              (1 / (2 : ℝ) ^ l) ^ b := by
          rw [← Real.rpow_add (by positivity :
            0 < (1 / (2 : ℝ) ^ N))]
    rw [hreal]
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast]
    conv_lhs =>
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
      rw [Real.mul_rpow (by positivity) (by positivity)]
      rw [Real.mul_rpow (by positivity) (by positivity)]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
    rw [← ofReal_inv_two_pow, ← ofReal_inv_two_pow]
    have hNpow :
        ENNReal.ofReal (((1 / (2 : ℝ) ^ N) ^ (a + b)) ^ (q : ℝ)) =
          ENNReal.ofReal (1 / (2 : ℝ) ^ N) ^ ((q : ℝ) * (a + b)) := by
      calc
        _ = ENNReal.ofReal ((1 / (2 : ℝ) ^ N) ^
            ((a + b) * (q : ℝ))) := by
          congr 1
          rw [Real.rpow_mul (by positivity)]
        _ = ENNReal.ofReal ((1 / (2 : ℝ) ^ N) ^
            ((q : ℝ) * (a + b))) := by
          congr 2
          ring
        _ = _ := (ENNReal.ofReal_rpow_of_nonneg (by positivity)
          (by positivity)).symm
    have hLpow :
        ENNReal.ofReal (((1 / (2 : ℝ) ^ l) ^ b) ^ (q : ℝ)) =
          ENNReal.ofReal (1 / (2 : ℝ) ^ l) ^ ((q : ℝ) * b) := by
      calc
        _ = ENNReal.ofReal ((1 / (2 : ℝ) ^ l) ^
            (b * (q : ℝ))) := by
          congr 1
          rw [Real.rpow_mul (by positivity)]
        _ = ENNReal.ofReal ((1 / (2 : ℝ) ^ l) ^
            ((q : ℝ) * b)) := by
          congr 2
          ring
        _ = _ := (ENNReal.ofReal_rpow_of_nonneg (by positivity)
          (by positivity)).symm
    rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
    rw [hNpow, hLpow]
  exact hmain.trans_eq hrewrite

end RegularityStructures

end
