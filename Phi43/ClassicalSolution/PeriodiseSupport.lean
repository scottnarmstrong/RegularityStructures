/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.ClassicalSolution.Periodise

/-!
# Time support of the periodised mollifier

This is the radial time-support form used in the construction of the smooth regularised noise.
The interval support bound itself is proved with the periodisation.
-/

@[expose] public section

open MeasureTheory Set

namespace RegularityStructures.Phi43

theorem timeSupport_periodise (rho : ℝ × (Fin 3 → ℝ) → ℝ) (hrho : IsMollifier rho)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ R : ℝ, ∀ z : SpaceTime, R < |z.1| → periodise rho eps z = 0 := by
  obtain ⟨a, b, hab⟩ := periodise_eq_zero_outside_time_interval rho hrho heps
  refine ⟨max |a| |b|, ?_⟩
  intro z hz
  apply hab z
  by_cases hleft : z.1 < a
  · exact Or.inl hleft
  by_cases hright : b < z.1
  · exact Or.inr hright
  exfalso
  have hlow : a ≤ z.1 := le_of_not_gt hleft
  have hupp : z.1 ≤ b := le_of_not_gt hright
  have hneg : -max |a| |b| ≤ z.1 := by
    calc
      -max |a| |b| ≤ -|a| := neg_le_neg (le_max_left _ _)
      _ ≤ a := neg_abs_le a
      _ ≤ z.1 := hlow
  have hpos : z.1 ≤ max |a| |b| := by
    exact hupp.trans (le_trans (le_abs_self b) (le_max_right _ _))
  exact (not_lt_of_ge (abs_le.2 ⟨hneg, hpos⟩)) hz

end RegularityStructures.Phi43

end
