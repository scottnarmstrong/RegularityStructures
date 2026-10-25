/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# The Littlewood–Paley bump

The smooth bump `χ` on `ℝ`, equal to `1` on `[-1, 1]` and supported in `(-2, 2)`, from which the
dyadic partition of unity on the frequencies `ℤ³` is built. It is one of the definitions of the
Littlewood–Paley norm `torusLittlewoodPaleyENorm` of `B^η_{∞,∞}(T³)`, which
`closureNorm_equiv_littlewoodPaley` compares with the norm of the statement. It coincides with
`RegularityStructures.torusLPBump`.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- The fixed bump of the Littlewood–Paley partition: `1` on `[-1, 1]`, `0` outside `(-2, 2)`. -/
def Statements.torusLPBump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, by norm_num⟩

end RegularityStructures.Phi43

end
