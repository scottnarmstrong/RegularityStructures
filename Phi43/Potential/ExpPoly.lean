/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Integrability of `e^{-(t - r)} (1 + |r|)^n` on `(-∞, t]`

The massive heat kernel damps the time lag exponentially, so a polynomial time growth of the
forcing is integrable against it: `integrableOn_exp_mul_pow_Iic`.
-/

public section

open MeasureTheory Set Filter Real Topology Asymptotics

namespace RegularityStructures.Potential

theorem isBigO_pow_exp_half (n : ℕ) :
    (fun x : ℝ => (1 + |x|) ^ n) =O[atTop] fun x : ℝ => exp ((1 / 2 : ℝ) * x) := by
  refine Asymptotics.IsBigO.of_bound (2 ^ n * n.factorial * exp (1 / 2)) ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [Real.norm_of_nonneg (pow_nonneg (by positivity) _), Real.norm_of_nonneg (exp_pos _).le,
    abs_of_nonneg hx]
  have h := Real.pow_div_factorial_le_exp ((1 + x) / 2) (by positivity) n
  have h2 : ((1 + x) / 2) ^ n / n.factorial ≤ exp ((1 + x) / 2) := h
  have hf : (0 : ℝ) < n.factorial := Nat.cast_pos.2 (Nat.factorial_pos n)
  rw [div_le_iff₀ hf] at h2
  have e : exp ((1 + x) / 2) = exp (1 / 2) * exp (1 / 2 * x) := by
    rw [← exp_add]; congr 1; ring
  calc (1 + x) ^ n = 2 ^ n * ((1 + x) / 2) ^ n := by rw [← mul_pow]; congr 1; ring
    _ ≤ 2 ^ n * (exp ((1 + x) / 2) * n.factorial) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by rw [e]; ring

theorem integrableOn_exp_mul_pow_Iic (t : ℝ) (n : ℕ) :
    IntegrableOn (fun r : ℝ => exp (-(t - r)) * (1 + |r|) ^ n) (Iic t) := by
  have h := integrableOn_exp_neg_mul_of_isBigO_exp (a := 1 / 2) (b := 1) (c := -t)
    (f := fun x => (1 + |x|) ^ n)
    ((by fun_prop : Continuous fun x : ℝ => (1 + |x|) ^ n).locallyIntegrable.locallyIntegrableOn _)
    (isBigO_pow_exp_half n) (by norm_num)
  have h1 : IntegrableOn (fun x : ℝ => exp (-t) * (exp (-1 * x) * (1 + |x|) ^ n)) (Ici (-t)) :=
    h.const_mul _
  have h2 := IntegrableOn.comp_neg_Iic (c := t) h1
  refine h2.congr_fun (fun r _ => ?_) measurableSet_Iic
  simp only [neg_mul, one_mul, neg_neg, abs_neg]
  rw [← mul_assoc, ← exp_add]
  congr 2
  ring

end RegularityStructures.Potential

end
