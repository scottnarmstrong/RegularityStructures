/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43Statements.Defs.TorusLittlewoodPaleyBlock

/-!
# The Littlewood–Paley norm

The Littlewood–Paley norm `sup_n 2^{nη} ‖Δ_n f‖_∞` of the Hölder–Besov space `B^η_{∞,∞}(T³)`, as an
extended real. `closureNorm_equiv_littlewoodPaley` shows that for `η < 0` it is equivalent on
`C(T³)` to the norm `‖·‖_η` of the statement, equation (2.3). It coincides with
`RegularityStructures.torusLittlewoodPaleyENorm`.

Source: the statement, Definition 2.1 and the remark after it.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

open scoped ENNReal

/-- The Littlewood–Paley norm of `B^η_{∞,∞}(T³)`: `sup_n 2^{nη} ‖Δ_n f‖_∞`. -/
def Statements.torusLittlewoodPaleyENorm (η : ℝ) (f : C(RegularityStructures.Torus3, ℝ)) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((n : ℝ) * η)) *
    ‖RegularityStructures.Phi43.Statements.torusLittlewoodPaleyBlock n f‖ₑ

end RegularityStructures.Phi43

end
