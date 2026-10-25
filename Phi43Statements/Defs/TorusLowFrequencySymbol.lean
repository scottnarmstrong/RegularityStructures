/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43Statements.Defs.TorusLPBump
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# The low-frequency symbols

The symbol `∏ᵢ χ(2^{-n} kᵢ)` of the projection onto frequencies of size up to about `2^n`, for the
tensor-product partition built from the bump `χ = torusLPBump`. It is one of the definitions of the
Littlewood–Paley norm `torusLittlewoodPaleyENorm` of `B^η_{∞,∞}(T³)`, which
`closureNorm_equiv_littlewoodPaley` compares with the norm of the statement. It coincides with
`RegularityStructures.torusLowFrequencySymbol`.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- The low-frequency symbol `∏ᵢ χ(2^{-n} kᵢ)` of the tensor-product Littlewood–Paley partition. -/
def Statements.torusLowFrequencySymbol (n : ℕ) (k : Fin 3 → ℤ) : ℝ :=
  ∏ i : Fin 3, RegularityStructures.Phi43.Statements.torusLPBump (((2 : ℝ) ^ n)⁻¹ * (k i : ℝ))

end RegularityStructures.Phi43

end
