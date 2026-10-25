/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Annihilating.Scaled
public import RegularityStructures.Analysis.Heat.Decomposition
public import RegularityStructures.Analysis.Heat.Decomposition.MomentDegree

/-!
# Derivative bounds for the scaled shells

`exists_abs_kernelDeriv_scaledShell_le`: the mixed derivatives `D₁^k D₂^l` of
`(x, y) ↦ scaledShell h n (x - y)` are bounded by `C (2^n)^{3 + |k|_𝔰 + |l|_𝔰}`.

Source: [Hai14, Assumption 5.1].
-/

@[expose] public noncomputable section

namespace RegularityStructures

end RegularityStructures

end

public section

open scoped ContDiff

namespace RegularityStructures

theorem exists_abs_lineIter_le {g : ParabolicSpace → ℝ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (L : List ParabolicSpace) : ∃ B, ∀ w, |lineIter L g w| ≤ B := by
  obtain ⟨B, hB⟩ := (contDiff_lineIter hg L).continuous.bounded_above_of_compact_support
    (hasCompactSupport_lineIter hc L)
  exact ⟨B, fun w => by simpa using hB w⟩

theorem exists_abs_kernelDeriv_scaledShell_le {h : ParabolicSpace → ℝ} (h0 : ContDiff ℝ ∞ h)
    (hs : ∀ z, 1 < parabolicNorm z → h z = 0) (k l : Fin 4 →₀ ℕ) :
    ∃ C : ℝ, ∀ n x y,
      |kernelDeriv k l (fun x y => scaledShell h n (x - y)) x y| ≤
        C * (2 : ℝ) ^ ((5 - (2 : ℝ) + multiDeg l + multiDeg k) * n) := by
  set J : List (Fin 4) := (Finsupp.toMultiset k).toList ++ (Finsupp.toMultiset l).toList with hJ
  have hdirs : multiDirs k ++ multiDirs l = J.map coordDir := by
    simp [hJ, multiDirs_eq_map]
  have hw : indexWeight J = multiDeg k + multiDeg l := by
    simp [hJ, indexWeight_append, indexWeight_toList]
  have hcs : HasCompactSupport h :=
    HasCompactSupport.intro (isCompact_parabolicNorm_le 1) fun _ hz => hs _ (not_le.1 hz)
  obtain ⟨B, hB⟩ := exists_abs_lineIter_le h0 hcs (J.map coordDir)
  refine ⟨B, fun n x y => ?_⟩
  have hc : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) n
  rw [kernelDeriv_sub (contDiff_scaledShell h0 n), hdirs, lineIter_coordDir_scaledShell h0, abs_mul,
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
