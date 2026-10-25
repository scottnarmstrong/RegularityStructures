/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43Statements.Defs.TorusLowFrequencySymbol

/-!
# The dyadic Littlewood–Paley symbols

The symbols of the dyadic blocks: block `0` is the low-frequency symbol at level `0`, and block
`n + 1` is the difference of the low-frequency symbols at levels `n + 1` and `n`. They sum to `1`
on `ℤ³`. It is one of the definitions of the Littlewood–Paley norm `torusLittlewoodPaleyENorm` of
`B^η_{∞,∞}(T³)`, which `closureNorm_equiv_littlewoodPaley` compares with the norm of the
statement. It coincides with `RegularityStructures.torusDyadicFrequencySymbol`.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

/-- The dyadic Littlewood–Paley symbols: block `0` is the low-frequency symbol, block `n + 1` the
difference of consecutive low-frequency symbols. -/
def Statements.torusDyadicFrequencySymbol : ℕ → (Fin 3 → ℤ) → ℝ
  | 0, k => RegularityStructures.Phi43.Statements.torusLowFrequencySymbol 0 k
  | n + 1, k => RegularityStructures.Phi43.Statements.torusLowFrequencySymbol (n + 1) k -
      RegularityStructures.Phi43.Statements.torusLowFrequencySymbol n k

end RegularityStructures.Phi43

end
