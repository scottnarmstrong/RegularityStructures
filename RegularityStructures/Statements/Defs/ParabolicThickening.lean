/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.Basic

/-!
# The parabolic thickening of a set

The closed parabolic `1`-neighbourhood `{z : ∃ y ∈ S, |z - y| ≤ 1}` of a set `S` of space-time
points, with `|·|` the parabolic norm. Local bounds on `S` that involve the model at nearby points
are stated with the model norm on this set.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The closed parabolic `1`-fattening of a set. -/
def parabolicThickening (S : Set RegularityStructures.ParabolicSpace) :
    Set RegularityStructures.ParabolicSpace :=
  {z | ∃ y ∈ S, RegularityStructures.parabolicNorm (z - y) ≤ 1}

end RegularityStructures

end
