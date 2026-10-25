/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Constants.Finite

/-!
# The deterministic convolution identity used by stochastic Fubini

The mollifier-at-`w` kernel is `ρ_ε^♯(w - ·)`.  Translation invariance of the space-time Haar
measure therefore identifies its convolution with the massive heat kernel with the mollified
kernel `G_ε(z - ·)`.  This is the deterministic identity needed when the stochastic Fubini
theorem is applied to a pathwise regularised noise.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

theorem integral_massiveHeatKernel_mul_mollifierAt_eq_mollifiedKernel
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) {ε : ℝ} (z v : SpaceTime) :
    ∫ w : SpaceTime, massiveHeatKernel (z - w) * mollifierAt ρ ε w v =
      mollifiedKernel ρ ε (z - v) := by
  have h := integral_comp_add_left_spaceTime
    (fun w : SpaceTime =>
      massiveHeatKernel ((z - v) - w) * periodise ρ ε w) (-v)
  calc
    ∫ w : SpaceTime, massiveHeatKernel (z - w) * mollifierAt ρ ε w v =
        ∫ w : SpaceTime,
          massiveHeatKernel ((z - v) - (-v + w)) * periodise ρ ε (-v + w) := by
      apply integral_congr_ae
      filter_upwards [] with w
      simp [mollifierAt, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    _ = ∫ w : SpaceTime,
        massiveHeatKernel ((z - v) - w) * periodise ρ ε w := h
    _ = mollifiedKernel ρ ε (z - v) := by rfl

end RegularityStructures.Phi43

end
