/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.Basic

/-!
# `GlobalPhi43.mwCylinder`

The unit past cylinder `P`. Source: MW20 (2.3)
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace GlobalPhi43

open RegularityStructures

/-- The cylinder `P = (0,1) × (−1,1)³` (MW20 (2.3)). -/
def mwCylinder : Set ParabolicSpace :=
  Set.Ioo (0 : ℝ) 1 ×ˢ {x | ‖x‖ < 1}

end GlobalPhi43

end
