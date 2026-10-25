/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HolderBesov

/-!
# Hölder–Besov norm of a uniformly bounded function

For `η ≤ 0`, the Hölder–Besov extended norm of `g ∈ C(T³)` is at most the supremum bound of `g`.
-/

public section

namespace RegularityStructures.Phi43.TimeSlice

open RegularityStructures
open scoped ENNReal

/-- A uniform bound `|g y| ≤ A` bounds the Hölder–Besov extended norm of order `η ≤ 0`. -/
theorem holderBesovENorm_le_ofReal_of_abs_le {η : ℝ} (hη : η ≤ 0) (g : C(Torus3, ℝ)) {A : ℝ}
    (hA : 0 ≤ A) (h : ∀ y, |g y| ≤ A) : holderBesovENorm η g ≤ ENNReal.ofReal A := by
  refine (holderBesovENorm_le hη g).trans ?_
  rw [← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  exact (ContinuousMap.norm_le g hA).2 fun y => by simpa using h y

end RegularityStructures.Phi43.TimeSlice

end
