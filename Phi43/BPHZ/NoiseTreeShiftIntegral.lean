/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.Basic

/-!
# Integrals of dominated functions

`integral_le_of_measurable_le`: a nonnegative measurable function on `ℝ × T³` dominated by an
integrable one is integrable and has the smaller integral. This is the comparison step of the
`L²` translation estimates for test functions.
-/

public section

open MeasureTheory Set

namespace RegularityStructures.Phi43

/-- A measurable function dominated by an integrable one is integrable and has smaller integral. -/
theorem integral_le_of_measurable_le {G H : SpaceTime → ℝ} (hG : Measurable G)
    (hH : Integrable H) (h0 : ∀ u, 0 ≤ G u) (hGH : ∀ u, G u ≤ H u) :
    Integrable G ∧ ∫ u, G u ≤ ∫ u, H u := by
  have hint : Integrable G := hH.mono' hG.aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (h0 u)]
      exact hGH u)
  exact ⟨hint, integral_mono hint hH hGH⟩

end RegularityStructures.Phi43

end
