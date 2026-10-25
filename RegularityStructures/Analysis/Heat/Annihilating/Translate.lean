/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Annihilating.Moment

/-!
# Translating polynomials without raising the parabolic degree

If `P` has parabolic degree `≤ r` then `w ↦ P(x - w)` is again a polynomial of parabolic degree
`≤ r` (`exists_eval_sub_eq`).  A function `F` with vanishing moments against all monomials of
parabolic degree `< N` is therefore orthogonal to every polynomial `P(x - ·)` with `P` of degree `< N`.
-/

public section

open MeasureTheory

namespace RegularityStructures

theorem parabolicCoords_sub_apply (x w : ParabolicSpace) (i : Fin 4) :
    parabolicCoords (x - w) i = parabolicCoords x i - parabolicCoords w i := by
  fin_cases i <;> simp [parabolicCoords]

end RegularityStructures

end
