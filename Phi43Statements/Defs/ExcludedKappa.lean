/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.Interval.Set.Defs

/-!
# The excluded values of `κ`

The finite set `E ⊂ (0, 1/16)` of the numbers `(m/2 - n)/b` with `b ∈ {1, …, 16}`,
`n ∈ {0, …, 4}` and `m ∈ ℤ`. A non-polynomial symbol of degree at most `4` in the Φ⁴₃ regularity
structure has at most `16` noises, and its degree has the form `k/2 - bκ` with `k ∈ ℤ` and `b` the
number of noises. So every `κ ∈ (0, 1/16)` at which such a symbol has integer degree lies in `E`.
For `κ ∉ E` the integer-degree condition of the extension theorem [Hai14, Theorem 5.14] holds.
The set contains other values as well: avoiding it is sufficient, not necessary.

Source: [Hai14, Theorem 5.14].
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- The finite set of excluded values of `κ`:
`{(m/2 - n)/b : 1 ≤ b ≤ 16, 0 ≤ n ≤ 4, m ∈ ℤ} ∩ (0, 1/16)`. -/
def Statements.excludedKappa : Set ℝ :=
  {q : ℝ | ∃ b ∈ Finset.Icc (1 : ℕ) 16, ∃ n ∈ Finset.range 5, ∃ m : ℤ,
      q = ((m : ℝ) / 2 - (n : ℝ)) / (b : ℝ)} ∩ Set.Ioo (0 : ℝ) (1 / 16)

end RegularityStructures.Phi43

end
