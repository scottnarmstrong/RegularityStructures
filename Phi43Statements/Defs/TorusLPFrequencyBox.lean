/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Data.Int.Interval

/-!
# The frequency box of a dyadic block

The finite set of frequencies `k ∈ ℤ³` with `‖k‖_∞ ≤ 2^{n+1}`. It contains the support of the `n`-th
dyadic symbol, so each Littlewood–Paley block is a finite Fourier sum. It is one of the definitions
of the Littlewood–Paley norm `torusLittlewoodPaleyENorm` of `B^η_{∞,∞}(T³)`, which
`closureNorm_equiv_littlewoodPaley` compares with the norm of the statement. It coincides with
`RegularityStructures.torusLPFrequencyBox`.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- The frequency box `‖k‖_∞ ≤ 2^{n+1}` containing the support of the `n`-th block. -/
def Statements.torusLPFrequencyBox (n : ℕ) : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset fun _ : Fin 3 =>
    Finset.Icc (-((2 ^ (n + 1) : ℕ) : ℤ)) ((2 ^ (n + 1) : ℕ) : ℤ)

end RegularityStructures.Phi43

end
