/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.PositiveMomentGammaEntries
public import Phi43.BPHZ.GammaMomentDiffAll
public import Phi43.BPHZ.SemigroupTestMoment

/-!
# The torus size of a projected increment

`torusParabolicSize_spaceTimeProj_sub_le`: the parabolic size on the torus of
`proj y - proj x` is at most the parabolic distance `d(y, x)`. The moment bounds for `v₂`, `v₃`
are stated in the torus size of the increment; this lemma converts them into bounds in
`d(y, x)`, the form used for the random `Γ`-entries of the models on `ℝ⁴`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The torus size of the projected increment is at most `d(y, x)`. -/
theorem torusParabolicSize_spaceTimeProj_sub_le (y x : ParabolicSpace) :
    torusParabolicSize (spaceTimeProj y - spaceTimeProj x) ≤ parabolicSemigroup.scaleDist y x := by
  rw [← spaceTimeProj_sub]
  exact torusParabolicSize_spaceTimeProj_le (y - x)

end RegularityStructures.Phi43

end
