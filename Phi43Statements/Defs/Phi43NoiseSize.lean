/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HolderBesov

/-!
# The size of a potential

`N_(T)(ψ) = sup_{t ∈ [-1, T + 1]} ‖ψ(t)‖_η`, with `‖·‖_η` the norm of the statement, equation
(2.3). It is the potential part of the size `phi43Size` of a lift.

Source: the statement, equation (2.3).
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

open scoped ENNReal

/-- Noise size `N_(T)(ψ) = sup_{t ∈ [-1, T+1]} ‖ψ(t)‖_η`. -/
def Statements.phi43NoiseSize (η T : ℝ) (ψ : ℝ → C(RegularityStructures.Torus3, ℝ)) : ℝ≥0∞ :=
  ⨆ t ∈ Set.Icc (-1 : ℝ) (T + 1), RegularityStructures.holderBesovENorm η (ψ t)

end RegularityStructures.Phi43

end
