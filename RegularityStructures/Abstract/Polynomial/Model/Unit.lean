/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Polynomial.Model.Bounds
public import RegularityStructures.Abstract.Polynomial.Basic

/-!
# The unit multi-index

`polyZero hN` is the multi-index `0 ∈ PolyIndex N` (for `0 < N`), indexing the unit `X^0 = 1` of
the polynomial regularity structure, and `polyDeg_polyZero` records its degree `|0|_𝔰 = 0`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {N : ℕ}

/-- The multi-index `0`, of degree `0 < N`, indexing the unit `X^0 = 1`. -/
def polyZero (hN : 0 < N) : PolyIndex N := ⟨0, by simpa using hN⟩

theorem polyDeg_polyZero (hN : 0 < N) : polyDeg N (polyZero hN) = 0 := by
  simp [polyDeg, polyZero]

end RegularityStructures

end
