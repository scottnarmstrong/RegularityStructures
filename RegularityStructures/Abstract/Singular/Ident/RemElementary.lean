/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Ident.Integrals
public import RegularityStructures.Torus.Basic

/-!
# Elementary inequalities for the spatial decay estimates

For `v : Fin 3 → ℝ` write `l1 v = ∑ |v_i|`.  Elementary facts relating `‖v‖`, `l1 v`, `sqNorm3 v`
and `parabolicNorm`, used to compare the polynomial growth of the diagonal values `g_{y,j}(y)` with
the decay of the remainder kernel.
-/

public section

open Finset

namespace RegularityStructures

/-- `‖v‖ ≤ ∑ |v_i|`. -/
theorem norm_le_sum_abs (v : Fin 3 → ℝ) : ‖v‖ ≤ ∑ i, |v i| := by
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun j => |v j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)

theorem one_add_sum_abs_le_mul (x y : Fin 3 → ℝ) :
    1 + ∑ i, |y i| ≤ (1 + ∑ i, |x i|) * (1 + ∑ i, |x i - y i|) := by
  have h : ∑ i, |y i| ≤ ∑ i, |x i| + ∑ i, |x i - y i| := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    calc |y i| = |x i - (x i - y i)| := by ring_nf
      _ ≤ |x i| + |x i - y i| := abs_sub _ _
  have h1 : 0 ≤ ∑ i, |x i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h2 : 0 ≤ ∑ i, |x i - y i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  nlinarith

theorem sq_one_add_sum_abs_le (u : Fin 3 → ℝ) :
    (1 + ∑ i, |u i|) ^ 2 ≤ 6 * (1 + sqNorm3 u) := by
  simp only [sqNorm3, Fin.sum_univ_three]
  have h0 := abs_nonneg (u 0)
  have h1 := abs_nonneg (u 1)
  have h2 := abs_nonneg (u 2)
  have e0 := sq_abs (u 0)
  have e1 := sq_abs (u 1)
  have e2 := sq_abs (u 2)
  nlinarith [sq_nonneg (|u 0| - |u 1|), sq_nonneg (|u 1| - |u 2|), sq_nonneg (|u 0| - |u 2|),
    sq_nonneg (|u 0| + |u 1| + |u 2| - 1)]

theorem inv_one_add_sqNorm3_pow_le (u : Fin 3 → ℝ) (m : ℕ) :
    ((1 + sqNorm3 u)⁻¹) ^ m ≤ 6 ^ m * ((1 + ∑ i, |u i|)⁻¹) ^ (2 * m) := by
  have hQ : 0 ≤ sqNorm3 u := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hs : 0 ≤ ∑ i, |u i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h1 : (1 + sqNorm3 u)⁻¹ ≤ 6 * ((1 + ∑ i, |u i|)⁻¹) ^ 2 := by
    have hb : (1 + ∑ i, |u i|) ^ 2 ≤ 6 * (1 + sqNorm3 u) := sq_one_add_sum_abs_le u
    have hpos : 0 < (1 + ∑ i, |u i|) ^ 2 := by positivity
    calc (1 + sqNorm3 u)⁻¹ = 6 * (6 * (1 + sqNorm3 u))⁻¹ := by field_simp
      _ ≤ 6 * ((1 + ∑ i, |u i|) ^ 2)⁻¹ := by gcongr
      _ = 6 * ((1 + ∑ i, |u i|)⁻¹) ^ 2 := by rw [inv_pow]
  calc ((1 + sqNorm3 u)⁻¹) ^ m ≤ (6 * ((1 + ∑ i, |u i|)⁻¹) ^ 2) ^ m :=
        pow_le_pow_left₀ (by positivity) h1 m
    _ = 6 ^ m * ((1 + ∑ i, |u i|)⁻¹) ^ (2 * m) := by rw [mul_pow, ← pow_mul]

theorem one_add_parabolicNorm_le_two_mul_of_slab {y : ParabolicSpace} (h0 : 0 < y.1) (h1 : y.1 ≤ 1) :
    1 + parabolicNorm y ≤ 2 * (1 + ∑ i, |y.2 i|) := by
  unfold parabolicNorm
  have : Real.sqrt |y.1| ≤ 1 := by
    rw [abs_of_pos h0]
    calc Real.sqrt y.1 ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h1
      _ = 1 := Real.sqrt_one
  have h2 : 0 ≤ ∑ i, |y.2 i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  linarith

end RegularityStructures
