/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Decomposition.Moment

/-!
# The heat kernel decomposition satisfies Assumption 5.1 with `β = 2`

`isRegularisingDecomposition_heatShell : IsRegularisingDecomposition (fun n x y => heatShell n (x - y)) 2`.

Source: Hairer, arXiv:1303.5113v4, Lemma 5.5 and Assumption 5.1 ((5.3)–(5.5)).
-/

public section

open MeasureTheory
open scoped ContDiff

namespace RegularityStructures

theorem monoFn_neg (l : Fin 4 → ℕ) (z : ParabolicSpace) :
    monoFn l (-z) = (-1 : ℝ) ^ (∑ i, l i) * monoFn l z := by
  have hc : ∀ i, parabolicCoords (-z) i = -parabolicCoords z i := by
    intro i; fin_cases i <;> simp [parabolicCoords]
  unfold monoFn
  have hp : ∀ i, parabolicCoords (-z) i ^ l i =
      (-1 : ℝ) ^ l i * parabolicCoords z i ^ l i := fun i => by rw [hc i]; ring
  simp only [hp, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum]

theorem multiDirs_zero : multiDirs 0 = [] := by simp [multiDirs]

end RegularityStructures

end
