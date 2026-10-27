/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.SectionDifferentials

/-! The derivative of the complete second-variable section and its exact
spatial coefficient on the diagonal. -/
@[expose] public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20

def sectionSecondInsert : ParabolicSpace →L[ℝ] GermPoint :=
  (0 : ParabolicSpace →L[ℝ] ParabolicSpace).prod (ContinuousLinearMap.id ℝ ParabolicSpace)

def sectionSecondDerivative (U : GermPoint → ℝ) (p : GermPoint) : ParabolicSpace →L[ℝ] ℝ :=
  (fderiv ℝ U p).comp sectionSecondInsert

theorem section_hasFDerivAt (U : GermPoint → ℝ) (x y : ParabolicSpace)
    (hU : DifferentiableAt ℝ U (x, y)) :
    HasFDerivAt (fun z => U (x, z)) (sectionSecondDerivative U (x, y)) y := by
  exact hU.hasFDerivAt.comp y ((hasFDerivAt_const x y).prodMk (hasFDerivAt_id y))

theorem diagonalCoefficient_eq_second_derivative (U : GermPoint → ℝ) (x : ParabolicSpace)
    (hU : DifferentiableAt ℝ U (x, x)) :
    diagonalSpatialCoefficient U x = fun i => sectionSecondDerivative U (x, x) (0, Pi.single i 1) := by
  funext i
  rw [diagonalSpatialCoefficient_eq_fderiv_local U x hU i]
  simp [sectionSecondDerivative, sectionSecondInsert]

end GlobalPhi43.Local
