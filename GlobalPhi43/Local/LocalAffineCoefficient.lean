/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.MW20.OptimalAffineCoefficient

/-! Canonical coefficient selection requires differentiability only at the
actual diagonal point, not a globally smooth extension of the germ. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Set

/-- Local differentiability supplies the derivative of each short coordinate ray. -/
theorem hasDerivAt_diagonalSpatialCoefficient_local
    (U : ParabolicSpace × ParabolicSpace → ℝ) (x : ParabolicSpace)
    (hU : DifferentiableAt ℝ U (x, x)) (i : Fin 3) :
    HasDerivAt (fun t => U (x, spatialCoordinateLine x i t))
      (diagonalSpatialCoefficient U x i) 0 := by
  have hl : DifferentiableAt ℝ (fun t : ℝ => (x, spatialCoordinateLine x i t)) 0 := by
    unfold spatialCoordinateLine
    fun_prop
  have hU' : DifferentiableAt ℝ U (x, spatialCoordinateLine x i 0) := by
    simpa only [spatialCoordinateLine, zero_smul, add_zero] using hU
  exact (hU'.comp 0 hl).hasDerivAt

end GlobalPhi43.Local
