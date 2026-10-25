/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.Kernel.TimeTaylorBound
public import RegularityStructures.Analysis.Parabolic.SingularKernel
public import RegularityStructures.Analysis.Parabolic.Polynomial

/-!
# Norms of iterated derivatives from coordinate words

For smooth `f` on `ℝ × ℝ³`, `‖D^n f(u)‖ ≤ 4^n b` as soon as every iterated derivative along a word
of coordinate directions (`lineIter (List.ofFn fun i => coordDir (r i)) f u`, `r : Fin n → Fin 4`)
is bounded by `b` (`norm_iteratedFDeriv_le_of_words`).
-/

public section

open scoped ContDiff

namespace RegularityStructures

theorem eq_sum_parabolicCoords_smul_coordDir (d : ParabolicSpace) :
    d = ∑ c : Fin 4, parabolicCoords d c • coordDir c := by
  have h1 : coordDir 1 = spaceDir 0 := rfl
  have h2 : coordDir 2 = spaceDir 1 := rfl
  have h3 : coordDir 3 = spaceDir 2 := rfl
  ext
  · simp [Fin.sum_univ_four, parabolicCoords, coordDir_zero, h1, h2, h3, timeDir, spaceDir]
  · rename_i i
    fin_cases i <;>
      simp [Fin.sum_univ_four, parabolicCoords, coordDir_zero, h1, h2, h3, timeDir, spaceDir]

theorem abs_parabolicCoords_le_norm (d : ParabolicSpace) (c : Fin 4) :
    |parabolicCoords d c| ≤ ‖d‖ := by
  have h1 : |d.1| ≤ ‖d‖ := by
    rw [← Real.norm_eq_abs]; exact norm_fst_le d
  have h2 : ∀ i : Fin 3, |d.2 i| ≤ ‖d‖ := fun i => by
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm d.2 i).trans (norm_snd_le d)
  fin_cases c
  · simpa [parabolicCoords] using h1
  · simpa [parabolicCoords] using h2 0
  · simpa [parabolicCoords] using h2 1
  · simpa [parabolicCoords] using h2 2

/-- The norm of `D^n f(u)` is at most `4^n b` if every coordinate word derivative is at most `b`. -/
theorem norm_iteratedFDeriv_le_of_words {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f) (n : ℕ)
    (u : ParabolicSpace) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ r : Fin n → Fin 4, |lineIter (List.ofFn fun i => coordDir (r i)) f u| ≤ b) :
    ‖iteratedFDeriv ℝ n f u‖ ≤ 4 ^ n * b := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
  have e : m = fun i => ∑ c : Fin 4, parabolicCoords (m i) c • coordDir c := by
    funext i; exact eq_sum_parabolicCoords_smul_coordDir (m i)
  have e' : (iteratedFDeriv ℝ n f u) m =
      (iteratedFDeriv ℝ n f u) (fun i => ∑ c : Fin 4, parabolicCoords (m i) c • coordDir c) :=
    congrArg _ e
  rw [e', ContinuousMultilinearMap.map_sum, Real.norm_eq_abs]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ r : Fin n → Fin 4,
      |(iteratedFDeriv ℝ n f u) (fun i => parabolicCoords (m i) (r i) • coordDir (r i))| ≤
        b * ∏ i, ‖m i‖ := by
    intro r
    rw [(iteratedFDeriv ℝ n f u).map_smul_univ, smul_eq_mul, abs_mul,
      iteratedFDeriv_apply_eq_lineIter_ofFn hf, Finset.abs_prod]
    rw [mul_comm]
    refine mul_le_mul (h r) ?_ (Finset.prod_nonneg fun _ _ => abs_nonneg _) hb
    exact Finset.prod_le_prod₀ (fun i _ => abs_nonneg (parabolicCoords (m i) (r i)))
      (fun i _ => abs_parabolicCoords_le_norm (m i) (r i))
  calc _ ≤ ∑ _r : Fin n → Fin 4, b * ∏ i, ‖m i‖ := Finset.sum_le_sum fun r _ => hterm r
    _ = 4 ^ n * b * ∏ i, ‖m i‖ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        Fintype.card_fin, nsmul_eq_mul]
      push_cast; ring

end RegularityStructures

end
