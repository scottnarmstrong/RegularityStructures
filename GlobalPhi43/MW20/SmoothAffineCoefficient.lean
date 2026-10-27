module

public import GlobalPhi43.MW20.OptimalAffineCoefficient
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Smoothness of the actual coefficient selected in (2.6). This supplies the
smooth ν needed by the smooth second-product germ, without a separate
coefficient regularity assumption. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures
open scoped ContDiff

/-- The coordinate-line definition is the corresponding component of the
spatial derivative in the second argument at the diagonal. -/
theorem diagonalSpatialCoefficient_eq_fderiv
    (U : ParabolicSpace × ParabolicSpace → ℝ) (hU : ContDiff ℝ ∞ U)
    (x : ParabolicSpace) (i : Fin 3) :
    diagonalSpatialCoefficient U x i =
      fderiv ℝ U (x, x) (0, (0, Pi.single i (1 : ℝ))) := by
  have hl : HasDerivAt (fun t : ℝ => (x, spatialCoordinateLine x i t))
      ((0 : ParabolicSpace), (0, Pi.single i (1 : ℝ))) 0 := by
    have hs := (hasDerivAt_const (0 : ℝ) x.2).add
      ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i (1 : ℝ)))
    simpa only [spatialCoordinateLine, zero_add, one_smul, Pi.add_apply, id_eq] using
      (hasDerivAt_const (0 : ℝ) x).prodMk
        ((hasDerivAt_const (0 : ℝ) x.1).prodMk hs)
  have hd : HasFDerivAt U (fderiv ℝ U (x, x)) (x, spatialCoordinateLine x i 0) := by
    simpa only [spatialCoordinateLine, zero_smul, add_zero] using
      (hU.differentiable (by simp)).differentiableAt.hasFDerivAt (x := (x, x))
  exact (hasDerivAt_diagonalSpatialCoefficient U hU x i).unique (hd.comp_hasDerivAt 0 hl)

/-- Source smoothness of the germ supplies smoothness of its optimal affine
coefficient. No independent smooth-ν premise is required. -/
theorem diagonalSpatialCoefficient_contDiff
    (U : ParabolicSpace × ParabolicSpace → ℝ) (hU : ContDiff ℝ ∞ U) :
    ContDiff ℝ ∞ (diagonalSpatialCoefficient U) := by
  apply contDiff_pi.2
  intro i
  have hd := hU.contDiff_fderiv_apply (m := ∞) (by simp)
  have hc : ContDiff ℝ ∞ (fun x : ParabolicSpace =>
      ((x, x), ((0 : ParabolicSpace), ((0 : ℝ), (Pi.single i (1 : ℝ) : Fin 3 → ℝ))))) := by fun_prop
  have hh := hd.comp hc
  simpa only [diagonalSpatialCoefficient_eq_fderiv U hU, Function.comp_def] using hh

end GlobalPhi43.MW20
