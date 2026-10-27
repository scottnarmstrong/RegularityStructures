/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.Basic

/-!
# `GlobalPhi43.parabolicDist`

The parabolic metric of MW20 (2.1). Source: MW20 §2.1, (2.1).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace GlobalPhi43

open RegularityStructures

/-- The parabolic metric `d((t,x),(t̄,x̄)) = max{√|t − t̄|, |x − x̄|_∞}` on `ℝ × ℝ³` (MW20 (2.1)).
The spatial norm is the sup norm of `Fin 3 → ℝ`. -/
def parabolicDist (z w : ParabolicSpace) : ℝ :=
  max (√|z.1 - w.1|) ‖z.2 - w.2‖

end GlobalPhi43

end
