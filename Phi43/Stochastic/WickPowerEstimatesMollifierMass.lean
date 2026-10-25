/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Torus.KernelBoundsPeriodiseL1
public import Phi43.Constants.Finite

/-!
# Signed mass preservation of the torus mollifier

The spatial periodisation preserves the integral, including for signed mollifiers.
The proof unfolds the fundamental domain and then uses the Euclidean parabolic
change of variables. This supplies the cancellation needed in mollification increments.
-/

public section

open MeasureTheory Set Submodule

namespace RegularityStructures.Phi43

theorem wick_integral_rescale_eq_one
    {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ)
    {ε : ℝ} (hε : 0 < ε) : ∫ z, rescale ρ ε z = 1 := by
  have heq : rescale ρ ε = rescaledTestFunction ρ ε 0 := by
    funext z
    simp [rescale, rescaledTestFunction, parabolicDilate, zpow_neg, inv_pow]
  rw [heq, integral_rescaledTestFunction ρ hε 0, hρ.integral_eq_one]

end RegularityStructures.Phi43

end
