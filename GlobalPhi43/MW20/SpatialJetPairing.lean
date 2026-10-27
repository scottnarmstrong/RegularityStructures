module

public import GlobalPhi43.MW20.SmoothAffineCoefficient
public import Mathlib.Algebra.BigOperators.Pi

/-!
# The exact spatial pairing in the canonical source derivative
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures
open scoped ContDiff

/-- Expand a spatial continuous linear functional in the actual coordinate basis. -/
theorem clm_spatial_pairing (L : (ParabolicSpace × ParabolicSpace) →L[ℝ] ℝ)
    (s : Fin 3 → ℝ) :
    L (0, (0, s)) = ∑ i, L (0, (0, Pi.single i 1)) * s i := by
  have hs : ((0 : ParabolicSpace), ((0 : ℝ), s)) =
      ∑ i : Fin 3, s i • ((0 : ParabolicSpace), ((0 : ℝ), Pi.single i (1 : ℝ))) := by
    ext i <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  rw [hs, map_sum]
  simp only [map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Split the full diagonal derivative into its time direction and the exact
canonical spatial coefficient from (2.6). -/
theorem diagonal_derivative_split (U : ParabolicSpace × ParabolicSpace → ℝ)
    (hU : ContDiff ℝ ∞ U) (x y : ParabolicSpace) :
    fderiv ℝ U (x, x) (0, y - x) =
      (y.1 - x.1) * fderiv ℝ U (x, x) (0, (1, 0)) +
        ∑ i, diagonalSpatialCoefficient U x i * (y.2 i - x.2 i) := by
  have he : ((0 : ParabolicSpace), y - x) =
      (y.1 - x.1) • ((0 : ParabolicSpace), ((1 : ℝ), (0 : Fin 3 → ℝ))) +
        ((0 : ParabolicSpace), ((0 : ℝ), y.2 - x.2)) := by
    ext i <;> simp
  rw [he, map_add, map_smul, smul_eq_mul, clm_spatial_pairing]
  simp only [diagonalSpatialCoefficient_eq_fderiv U hU, Pi.sub_apply]

end GlobalPhi43.MW20
