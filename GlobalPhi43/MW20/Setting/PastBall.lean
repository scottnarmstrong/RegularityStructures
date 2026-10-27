/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import GlobalPhi43.MW20.Setting.ParabolicDist

/-!
# `GlobalPhi43.pastBall`

Past parabolic balls. Source: MW20 (2.2)
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace GlobalPhi43

open RegularityStructures

/-- The past ball `B(z, R) = {w | d(z, w) < R, t_w < t_z}` (MW20 (2.2)). -/
def pastBall (z : ParabolicSpace) (R : ℝ) : Set ParabolicSpace :=
  {w | parabolicDist z w < R ∧ w.1 < z.1}

end GlobalPhi43

end
