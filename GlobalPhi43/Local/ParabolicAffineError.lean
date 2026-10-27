/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.ParabolicTaylor
public import GlobalPhi43.Local.PastAffineError
public import GlobalPhi43.Local.SpatialLinearRepresentation

/-! The caloric proof's Taylor step attached to the actual affine infimum.
The derivative bound is an explicit assumption. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures Set Metric
open scoped ENNReal

theorem pastAffineError_le_of_bound (f : ParabolicSpace → ℝ) (x : ParabolicSpace)
    (c : ℝ) (ν : Fin 3 → ℝ) {R E : ℝ}
    (hbound : ∀ y ∈ pastBall x R, |f y - spatialAffine x c ν y| ≤ E) :
    pastAffineError f x R ≤ ENNReal.ofReal E := by
  apply (iInf_le _ c).trans
  apply (iInf_le _ ν).trans
  apply iSup_le
  intro y
  apply iSup_le
  intro hy
  exact ENNReal.ofReal_le_ofReal (hbound y hy)

end GlobalPhi43.Local
