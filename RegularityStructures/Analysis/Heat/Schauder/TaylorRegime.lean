/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.TaylorKernel
public import RegularityStructures.Analysis.Heat.Schauder.TaylorPairing

/-!
# Large scales: smoothness, support and size of the Taylor profile

For `d = ‖y - x‖_𝔰 ≤ 2^{-n}` the profile `H = taylorProfile (scaledShell h n) σ (y - x)` is smooth,
supported in `‖u‖_𝔰 ≤ 2^{-n} + d` and has the bounds of this file; see `TaylorEstimate.lean`.
-/

public section

open MeasureTheory
open scoped ContDiff

namespace RegularityStructures

theorem abs_parabolicCoords_le {z : ParabolicSpace} (i : Fin 4) :
    |parabolicCoords z i| ≤ parabolicNorm z ^ parabolicWeight i := by
  have hs := Real.sqrt_nonneg |z.1|
  have h1 : ∀ i : Fin 3, |z.2 i| ≤ ∑ j, |z.2 j| := fun i =>
    Finset.single_le_sum (f := fun j => |z.2 j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have h0 : 0 ≤ ∑ j, |z.2 j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [parabolicCoords, parabolicWeight]
    have : |z.1| = Real.sqrt |z.1| ^ 2 := (Real.sq_sqrt (abs_nonneg _)).symm
    simp only [Matrix.cons_val_zero]
    rw [this]
    have : Real.sqrt |z.1| ≤ parabolicNorm z := by unfold parabolicNorm; linarith
    exact pow_le_pow_left₀ hs this 2
  · simp only [parabolicCoords, parabolicWeight]
    fin_cases i <;> simp <;> (unfold parabolicNorm; linarith [h1 0, h1 1, h1 2])

theorem multiDeg_eq_sum (k : Fin 4 →₀ ℕ) : multiDeg k = ∑ i, parabolicWeight i * k i := by
  unfold multiDeg
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [mul_comm]

theorem abs_coeffT_le {s : Fin 4 → ℝ} {d : ℝ} (hs : ∀ j, |s j| ≤ d ^ parabolicWeight j)
    (k : Fin 4 →₀ ℕ) : |coeffT s k| ≤ d ^ multiDeg k := by
  unfold coeffT
  rw [Finset.abs_prod]
  have : d ^ multiDeg k = ∏ i, d ^ (parabolicWeight i * k i) := by
    rw [Finset.prod_pow_eq_pow_sum, multiDeg_eq_sum]
  rw [this]
  refine Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => ?_
  rw [abs_div, abs_pow, Nat.abs_cast, pow_mul]
  calc |s i| ^ k i / ((Nat.factorial (k i) : ℕ) : ℝ) ≤ |s i| ^ k i := by
        refine div_le_self (pow_nonneg (abs_nonneg _) _) ?_
        exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
    _ ≤ (d ^ parabolicWeight i) ^ k i := pow_le_pow_left₀ (abs_nonneg _) (hs i) _

end RegularityStructures

end
