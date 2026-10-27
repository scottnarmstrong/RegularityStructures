/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.Basic

/-!
# `GlobalPhi43.mwInnerCylinder`

The inner cylinders `P_R`. Source: MW20 (2.3)
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace GlobalPhi43

open RegularityStructures

/-- The cylinder `P_R = (R², 1) × {x : |x|_∞ < 1 − R}` at parabolic distance `R` from the parabolic boundary of
`P`, with no inset from the terminal time (MW20 (2.3)). -/
def mwInnerCylinder (R : ℝ) : Set ParabolicSpace :=
  Set.Ioo (R ^ 2) 1 ×ˢ {x | ‖x‖ < 1 - R}

end GlobalPhi43

end
