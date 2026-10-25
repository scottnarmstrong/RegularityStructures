/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.BPHZ.GaussianWickDiagramIdentity
public import Mathlib.Data.Prod.Lex
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# Positions of a family of words

For words `L : Fin r → List (Fin n)` the positions are `WickPosition L = Σ j, Fin (L j).length`,
ordered lexicographically (block first).  A product over blocks of sums over involutions of the
positions of the block is a sum over *block involutions* of all positions
(`prod_wickMonomial_eq_sum_blockInvolutions`).
-/

@[expose] public noncomputable section

namespace RegularityStructures

variable {n r : ℕ}

/-- The positions of the words `L j`: pairs `(j, a)` with `a` a position in the word `L j`. -/
abbrev WickPosition (L : Fin r → List (Fin n)) : Type := Σ j : Fin r, Fin (L j).length

namespace WickPosition

variable (L : Fin r → List (Fin n))

instance : LinearOrder (WickPosition L) :=
  LinearOrder.lift' (fun c : WickPosition L => toLex ((c.1 : ℕ), (c.2 : ℕ)))
    (by
      rintro ⟨j, a⟩ ⟨j', b⟩ h
      have h1 := toLex_inj.1 h
      obtain ⟨h2, h3⟩ := Prod.mk.inj h1
      obtain rfl := Fin.ext h2
      obtain rfl := Fin.ext h3
      rfl)

variable {L}

/-- The position `a` of the word `L j`. -/
def mk (j : Fin r) (a : Fin (L j).length) : WickPosition L := ⟨j, a⟩

/-- The block of a position. -/
def block (c : WickPosition L) : Fin r := c.1

/-- The letter at a position. -/
def letter (c : WickPosition L) : Fin n := (L c.1).get c.2

end WickPosition

end RegularityStructures

end
