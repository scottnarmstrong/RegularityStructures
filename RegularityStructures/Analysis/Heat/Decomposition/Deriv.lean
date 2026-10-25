/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Decomposition.Scaling
public import RegularityStructures.Analysis.Heat.Decomposition.ScalingDeriv

/-!
# Derivative bounds for the heat shells

`|D₁^k D₂^l K_n(x, y)| ≤ C 2^{(5 - 2 + |l|_𝔰 + |k|_𝔰) n}` for `K_n(x, y) = heatShell n (x - y)`
[Hai14, (5.4)] with `β = 2`.
-/

public section

open scoped ContDiff

namespace RegularityStructures

theorem rpow_two_mul_nat (a : ℕ) (n : ℕ) :
    (2 : ℝ) ^ (((a : ℝ)) * (n : ℝ)) = ((2 : ℝ) ^ n) ^ a := by
  rw [← Nat.cast_mul, Real.rpow_natCast, mul_comm, pow_mul]

theorem exists_abs_kernelDeriv_heatShell_le (k l : Fin 4 →₀ ℕ) :
    ∃ C : ℝ, ∀ n x y,
      |kernelDeriv k l (fun x y => heatShell n (x - y)) x y| ≤
        C * (2 : ℝ) ^ ((5 - (2 : ℝ) + multiDeg l + multiDeg k) * n) := by
  set J : List (Fin 4) := (Finsupp.toMultiset k).toList ++ (Finsupp.toMultiset l).toList with hJ
  have hdirs : multiDirs k ++ multiDirs l = J.map coordDir := by
    simp [hJ, multiDirs_eq_map]
  have hw : indexWeight J = multiDeg k + multiDeg l := by
    simp [hJ, indexWeight_append, indexWeight_toList]
  obtain ⟨B, hB⟩ := exists_abs_lineIter_heatShell_le (J.map coordDir) 0
  refine ⟨B, fun n x y => ?_⟩
  have hc : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  rw [kernelDeriv_sub (contDiff_heatShell n), hdirs, lineIter_coordDir_heatShell, abs_mul,
    abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow, abs_of_pos hc, hw]
  have e : (2 : ℝ) ^ ((5 - (2 : ℝ) + multiDeg l + multiDeg k) * n) =
      ((2 : ℝ) ^ n) ^ (3 + (multiDeg k + multiDeg l)) := by
    rw [← rpow_two_mul_nat]
    congr 2
    push_cast
    ring
  rw [e, mul_comm B]
  exact mul_le_mul_of_nonneg_left (hB _) (by positivity)

end RegularityStructures

end
