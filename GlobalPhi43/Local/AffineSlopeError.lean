/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.ProbeDerivative

/-! The finite-scale error between a past-probe slope and an affine coefficient. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures

theorem affine_probe_slope_error (f : ParabolicSpace → ℝ) (x : ParabolicSpace)
    (c : ℝ) (ν : Fin 3 → ℝ) {R γ H : ℝ} (hR : 0 < R)
    (happrox : ∀ y ∈ pastBall x R, |f y - spatialAffine x c ν y| ≤ H * R ^ γ)
    (i : Fin 3) :
    |(f (coefficientProbe x (R / 4) i) - f (verticalProbe x (R / 4))) / (R / 4) - ν i| ≤
      8 * H * R ^ (γ - 1) := by
  have hi := happrox (coefficientProbe x (R / 4) i)
    (coefficientProbe_past (by linarith) (by linarith) i)
  have hzero := happrox (verticalProbe x (R / 4))
    (verticalProbe_past (by linarith) (by linarith))
  have heq : (f (coefficientProbe x (R / 4) i) - f (verticalProbe x (R / 4))) /
      (R / 4) - ν i =
      ((f (coefficientProbe x (R / 4) i) - spatialAffine x c ν (coefficientProbe x (R / 4) i)) -
       (f (verticalProbe x (R / 4)) - spatialAffine x c ν (verticalProbe x (R / 4)))) / (R / 4) := by
    have hp := spatialAffine_probe_difference x c ν (R / 4) i
    apply (eq_div_iff (by positivity : R / 4 ≠ 0)).2
    field_simp
    nlinarith
  rw [heq, abs_div, abs_of_pos (by linarith : 0 < R / 4)]
  calc
    _ ≤ (H * R ^ γ + H * R ^ γ) / (R / 4) := by
      apply div_le_div_of_nonneg_right _ (by linarith)
      exact (abs_sub _ _).trans (add_le_add hi hzero)
    _ = _ := by rw [Real.rpow_sub_one hR.ne']; field_simp; ring

end GlobalPhi43.Local
