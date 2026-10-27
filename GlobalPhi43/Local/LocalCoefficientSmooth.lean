/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.LocalAffineCoefficient
public import GlobalPhi43.MW20.SmoothAffineCoefficient

/-! Smoothness of the prescribed coefficient is local on the same open
source domain; a globally smooth germ is not required. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Set
open scoped ContDiff

theorem diagonalSpatialCoefficient_eq_fderiv_local
    (U : ParabolicSpace × ParabolicSpace → ℝ) (x : ParabolicSpace)
    (hU : DifferentiableAt ℝ U (x, x)) (i : Fin 3) :
    diagonalSpatialCoefficient U x i = fderiv ℝ U (x, x) (0, (0, Pi.single i 1)) := by
  have hl : HasDerivAt (fun t : ℝ => (x, spatialCoordinateLine x i t))
      ((0 : ParabolicSpace), (0, Pi.single i (1 : ℝ))) 0 := by
    have hs := (hasDerivAt_const (0 : ℝ) x.2).add
      ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i (1 : ℝ)))
    simpa only [spatialCoordinateLine, zero_add, one_smul, Pi.add_apply, id_eq] using
      (hasDerivAt_const (0 : ℝ) x).prodMk ((hasDerivAt_const (0 : ℝ) x.1).prodMk hs)
  have hd : HasFDerivAt U (fderiv ℝ U (x, x)) (x, spatialCoordinateLine x i 0) := by
    simpa only [spatialCoordinateLine, zero_smul, add_zero] using hU.hasFDerivAt
  exact (hasDerivAt_diagonalSpatialCoefficient_local U x hU i).unique (hd.comp_hasDerivAt 0 hl)

end GlobalPhi43.Local
