/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import GlobalPhi43.MW20.Setting.ParabolicDist

/-!
# `GlobalPhi43.parabolicClosedNbhd`

Closed parabolic neighbourhoods `S + B̄(0,r)`. Used for `P⁺ = P + B̄(0,1)` and `C + B̄(0, ρ₀)`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace GlobalPhi43

open RegularityStructures

/-- The closed `r`-neighbourhood `S + B̄(0, r) = {w | ∃ z ∈ S, d(z, w) ≤ r}` in the parabolic metric
(for example `P⁺ = P + B̄(0,1)` and `C + B̄(0, ρ₀)`). -/
def parabolicClosedNbhd (S : Set ParabolicSpace) (r : ℝ) : Set ParabolicSpace :=
  {w | ∃ z ∈ S, parabolicDist z w ≤ r}

end GlobalPhi43

end
