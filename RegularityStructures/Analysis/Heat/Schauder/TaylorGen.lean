/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Schauder.TaylorDeriv

/-!
# The generator commutes with derivatives, shifts and linear combinations

`parabolicGenerator` is a constant coefficient differential operator, hence it commutes with
`dirDeriv d` (`parabolicGenerator_dirDeriv`) and with shifts (`parabolicGenerator_shift`), and is
linear on smooth functions.
-/

public section

open scoped ContDiff

namespace RegularityStructures

theorem iterate_dirDeriv_dirDeriv {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f)
    (d e : ParabolicSpace) (n : ℕ) :
    (dirDeriv e)^[n] (dirDeriv d f) = dirDeriv d ((dirDeriv e)^[n] f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    exact dirDeriv_comm (contDiff_iterate_dirDeriv hf e n) e d

theorem parabolicGenerator_dirDeriv {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f)
    (d : ParabolicSpace) :
    parabolicGenerator (dirDeriv d f) = dirDeriv d (parabolicGenerator f) := by
  have hd := contDiff_dirDeriv hf d
  have e1 : parabolicGenerator f = fun y => generatorTimeCoeff * (dirDeriv timeDir)^[2] f y -
      generatorSpaceCoeff * ∑ i : Fin 3, (dirDeriv (spaceDir i))^[4] f y :=
    funext (parabolicGenerator_eq hf)
  have h2 := contDiff_iterate_dirDeriv hf timeDir 2
  have h4 : ∀ i : Fin 3, ContDiff ℝ ∞ ((dirDeriv (spaceDir i))^[4] f) := fun i =>
    contDiff_iterate_dirDeriv hf _ 4
  funext y
  rw [parabolicGenerator_eq hd, e1]
  have hs : ContDiff ℝ ∞ fun y => ∑ i : Fin 3, (dirDeriv (spaceDir i))^[4] f y :=
    ContDiff.sum fun i _ => h4 i
  rw [dirDeriv_sub (contDiff_const.mul h2) (contDiff_const.mul hs),
    dirDeriv_const_mul h2, dirDeriv_const_mul hs,
    dirDeriv_finset_sum Finset.univ (fun i _ => h4 i)]
  simp only [iterate_dirDeriv_dirDeriv hf]

end RegularityStructures

end
