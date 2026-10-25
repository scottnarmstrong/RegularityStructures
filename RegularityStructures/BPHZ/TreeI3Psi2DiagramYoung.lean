/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Young absorption of negative-power monomials

For positive reals `p, q, r`, `r ≤ 2`, and exponents `a, b, c ≥ 0` with `a + b + c ≤ E`, `E > 0`, the
monomial `p^(-a) q^(-b) r^(-c)` is at most `2^E (p^(-E) + q^(-E) + r^(-E))`.  This is the
weighted AM-GM inequality, followed by raising exponents on a variable bounded by `2`.  It is the
bookkeeping device by which the mixed products of centred powers produced by the diagram bounds
(`x^(-a) u^(-b)`, with `x = s(z - z')`, `u = s(z)`) are absorbed into the pairs of
[Hai14, p. 170--171].
-/

public section

namespace RegularityStructures

/-- Two-variable Young absorption in the exact-degree case. -/
theorem rpow_neg_mul_two_le {p q a b E : ℝ} (hp : 0 < p) (hq : 0 < q) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hE : 0 < E) (hab : a + b = E) : p ^ (-a) * q ^ (-b) ≤ p ^ (-E) + q ^ (-E) := by
  have hw := Real.geom_mean_le_arith_mean2_weighted (w₁ := a / E) (w₂ := b / E)
    (p₁ := p ^ (-E)) (p₂ := q ^ (-E)) (by positivity) (by positivity)
    (Real.rpow_nonneg hp.le _) (Real.rpow_nonneg hq.le _) (by field_simp; linarith)
  have e1 : (p ^ (-E)) ^ (a / E) = p ^ (-a) := by
    rw [← Real.rpow_mul hp.le]; congr 1; field_simp
  have e2 : (q ^ (-E)) ^ (b / E) = q ^ (-b) := by
    rw [← Real.rpow_mul hq.le]; congr 1; field_simp
  rw [e1, e2] at hw
  refine hw.trans ?_
  have n1 := Real.rpow_nonneg hp.le (-E)
  have n2 := Real.rpow_nonneg hq.le (-E)
  have w1 : a / E ≤ 1 := by rw [div_le_one hE]; linarith
  have w2 : b / E ≤ 1 := by rw [div_le_one hE]; linarith
  nlinarith [mul_le_mul_of_nonneg_right w1 n1, mul_le_mul_of_nonneg_right w2 n2]

end RegularityStructures

end
