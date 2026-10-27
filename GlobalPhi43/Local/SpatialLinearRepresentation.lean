/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.SmoothingComparison
public import Mathlib.LinearAlgebra.Pi

/-! Coordinates of a spatial differential in the source's exact affine form. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures
open scoped BigOperators

theorem spatial_differential_coordinates (L : (Fin 3 → ℝ) →L[ℝ] ℝ) (v : Fin 3 → ℝ) :
    L v = ∑ i, L (Pi.single i 1) * v i := by
  calc
    L v = L (∑ i, Pi.single i (v i)) := congrArg L (Finset.univ_sum_single v).symm
    _ = ∑ i, L (Pi.single i (v i)) := by rw [map_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      have he : (Pi.single i (v i) : Fin 3 → ℝ) = v i • Pi.single i 1 := by
        ext j
        by_cases h : j = i <;> simp [h]
      rw [he, map_smul, smul_eq_mul, mul_comm]

theorem spatialLinear_eq_differential (L : (Fin 3 → ℝ) →L[ℝ] ℝ) (w : ParabolicSpace) :
    spatialLinear (fun i => L (Pi.single i 1)) w = L w.2 :=
  (spatial_differential_coordinates L w.2).symm

end GlobalPhi43.Local
