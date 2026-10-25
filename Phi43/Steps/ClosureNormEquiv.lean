/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43Statements.Defs.TorusLittlewoodPaleyENorm
public import RegularityStructures.Torus.HolderBesovNormEquivalence

/-!
# The heat-semigroup norm and the Littlewood–Paley norm

For `η < 0`, the norm (2.3) of the statement and the Littlewood–Paley norm of `B^η_{∞,∞}(T³)` are
equivalent on `C(T³)`. The theorem `closureNorm_equiv_littlewoodPaley` has exactly the statement
`Statements.closureNorm_equiv_littlewoodPaley` of `Phi43Statements.Steps.ClosureNormEquiv`.

The Littlewood–Paley norm of the statement is a literal copy of the periodic Littlewood–Paley norm
of the library; the equivalence is proved by the heat-kernel multiplier and annular reconstruction
estimates.

Source: the statement, Definition 2.1 and the remark after it.
-/

public section

namespace RegularityStructures.Phi43

/-- Equivalence of the norm (2.3) of the statement and the Littlewood–Paley norm, for `η < 0`. -/
theorem closureNorm_equiv_littlewoodPaley (η : ℝ) (hη : η < 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : C(RegularityStructures.Torus3, ℝ),
      RegularityStructures.holderBesovENorm η f ≤
          ENNReal.ofReal C * RegularityStructures.Phi43.Statements.torusLittlewoodPaleyENorm η f ∧
        RegularityStructures.Phi43.Statements.torusLittlewoodPaleyENorm η f ≤
          ENNReal.ofReal C * RegularityStructures.holderBesovENorm η f := by
  exact RegularityStructures.holderBesovENorm_equiv_littlewoodPaley η hη

end RegularityStructures.Phi43

end
