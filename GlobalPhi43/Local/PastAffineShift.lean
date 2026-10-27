/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.PastAffineSubadditivity

/-! Exact affine-shift invariance of the actual affine approximation infimum. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures
open scoped ENNReal

 theorem spatialAffine_neg (x : ParabolicSpace) (c : ℝ) (ν : Fin 3 → ℝ) (y : ParabolicSpace) :
    spatialAffine x (-c) (-ν) y = -spatialAffine x c ν y := by
  simp only [spatialAffine, spatialLinear, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  ring

 theorem pastAffineError_affine_eq_zero (x : ParabolicSpace) (c : ℝ) (ν : Fin 3 → ℝ) (R : ℝ) :
    pastAffineError (spatialAffine x c ν) x R = 0 := by
  apply le_antisymm _ bot_le
  apply iInf_le_of_le c
  apply iInf_le_of_le ν
  simp

 theorem pastAffineError_add_affine (f : ParabolicSpace → ℝ) (x : ParabolicSpace)
    (c : ℝ) (ν : Fin 3 → ℝ) (R : ℝ) :
    pastAffineError (fun y => f y + spatialAffine x c ν y) x R = pastAffineError f x R := by
  have hf := pastAffineError_add_le f (spatialAffine x c ν) x R
  rw [pastAffineError_affine_eq_zero, add_zero] at hf
  have he : (fun y => (f y + spatialAffine x c ν y) + spatialAffine x (-c) (-ν) y) = f := by
    funext y
    rw [spatialAffine_neg]
    ring
  have hr := pastAffineError_add_le (fun y => f y + spatialAffine x c ν y)
    (spatialAffine x (-c) (-ν)) x R
  rw [he, pastAffineError_affine_eq_zero, add_zero] at hr
  exact le_antisymm hf hr

 theorem pastAffineError_sub_affine (f : ParabolicSpace → ℝ) (x : ParabolicSpace)
    (c : ℝ) (ν : Fin 3 → ℝ) (R : ℝ) :
    pastAffineError (fun y => f y - spatialAffine x c ν y) x R = pastAffineError f x R := by
  have he : (fun y => f y - spatialAffine x c ν y) =
      (fun y => f y + spatialAffine x (-c) (-ν) y) := by
    funext y
    rw [spatialAffine_neg]
    ring
  rw [he, pastAffineError_add_affine]

end GlobalPhi43.Local
