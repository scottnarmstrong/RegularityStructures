/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Decomposition.Support
public import RegularityStructures.Analysis.Parabolic.SingularKernel

/-!
# Derivative scaling of the heat shells

For a list `J` of coordinate indices (so `J.map coordDir` is a list of coordinate directions),
`D_J (heatShell n) (z) = (2^n)^{3 + |J|_𝔰} (D_J (heatShell 0)) (2^n z)`, and the mixed derivatives
`kernelDeriv k l (fun x y => h (x - y))` reduce to `(-1)^{|l|} D^{k,l} h (x - y)`.
-/

public section

open scoped ContDiff

namespace RegularityStructures

/-- The sum of the parabolic weights along a list of coordinate indices. -/
def indexWeight (J : List (Fin 4)) : ℕ := (J.map parabolicWeight).sum

@[simp]
theorem indexWeight_nil : indexWeight [] = 0 := by simp [indexWeight]

@[simp]
theorem indexWeight_cons (j : Fin 4) (J : List (Fin 4)) :
    indexWeight (j :: J) = parabolicWeight j + indexWeight J := by simp [indexWeight]

theorem indexWeight_append (J J' : List (Fin 4)) :
    indexWeight (J ++ J') = indexWeight J + indexWeight J' := by
  simp [indexWeight]

theorem indexWeight_toList (k : Fin 4 →₀ ℕ) :
    indexWeight (Finsupp.toMultiset k).toList = multiDeg k := by
  have key : ∀ k : Fin 4 →₀ ℕ, ((Finsupp.toMultiset k).map parabolicWeight).sum =
      Finsupp.weight parabolicWeight k := by
    intro k
    induction k using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp [Finsupp.toMultiset_add, hf, hg]
    | single a n =>
      simp [Finsupp.toMultiset_single, Finsupp.weight_apply, Multiset.map_nsmul,
        Multiset.sum_nsmul]
  rw [multiDeg, ← key]
  unfold indexWeight
  rw [← Multiset.sum_coe, ← Multiset.map_coe, Multiset.coe_toList]

theorem multiDirs_eq_map (k : Fin 4 →₀ ℕ) :
    multiDirs k = (Finsupp.toMultiset k).toList.map coordDir := rfl

theorem parabolicDilateCLM_coordDir (c : ℝ) (j : Fin 4) :
    parabolicDilateCLM c (coordDir j) = c ^ parabolicWeight j • coordDir j := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [coordDir_zero, timeDir, parabolicWeight, parabolicDilate, sq]
  · rw [coordDir_succ]
    have : parabolicWeight i.succ = 1 := by fin_cases i <;> rfl
    rw [this]
    simp [spaceDir, parabolicDilate]

theorem prod_map_pow (c : ℝ) (J : List (Fin 4)) :
    (J.map fun j => c ^ parabolicWeight j).prod = c ^ indexWeight J := by
  induction J with
  | nil => simp
  | cons j J ih => simp [ih, pow_add]

end RegularityStructures

end
