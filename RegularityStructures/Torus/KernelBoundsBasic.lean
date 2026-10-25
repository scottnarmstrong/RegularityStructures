/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Parabolic size on space-time over `T³`

The singular estimates for the massive heat kernel use the parabolic size
`|z|_s = |t|^(1/2) + |x|`, with the spatial point represented in the centred fundamental cube
`[-1/2,1/2)^3`.  The representative is defined here rather than changing the existing `[0,1)`
representative used by `heatKernel`.

Sources: [Hai14] = arXiv:1303.5113v4, §2 and Assumption 5.1; [Hos25] = arXiv:2310.07396v2, §2.1.
-/

@[expose] public noncomputable section

open Real Set

namespace RegularityStructures

/-- The centred representative of a point of `T³`, in `[-1/2,1/2)³`. -/
def torusCenteredRep (x : Torus3) : Fin 3 → ℝ := fun i =>
  if (1 / 2 : ℝ) ≤ torusRep x i then torusRep x i - 1 else torusRep x i

/-- The Euclidean spatial norm of the centred representative. -/
def torusSpatialNorm (x : Torus3) : ℝ := √(sqNorm3 (torusCenteredRep x))

/-- The parabolic size of a space-time point. -/
def torusParabolicSize (z : SpaceTime) : ℝ :=
  √|z.1| + torusSpatialNorm z.2

theorem torusRep_mem_Ico (x : Torus3) (i : Fin 3) : torusRep x i ∈ Ico (0 : ℝ) 1 := by
  change (AddCircle.equivIco (1 : ℝ) 0 (x i) : ℝ) ∈ Ico (0 : ℝ) 1
  simpa using (AddCircle.equivIco (1 : ℝ) 0 (x i)).property

theorem torusCenteredRep_mem_Ico (x : Torus3) (i : Fin 3) :
    torusCenteredRep x i ∈ Ico (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
  have hr := torusRep_mem_Ico x i
  unfold torusCenteredRep
  split_ifs with h
  · constructor <;> linarith [hr.1, hr.2]
  · constructor <;> linarith [hr.1, hr.2, h]

theorem torusCenteredRep_mem_Icc (x : Torus3) (i : Fin 3) :
    torusCenteredRep x i ∈ Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
  have h := torusCenteredRep_mem_Ico x i
  simp only [mem_Ico] at h
  exact ⟨h.1, h.2.le⟩

theorem torusSpatialNorm_nonneg (x : Torus3) : 0 ≤ torusSpatialNorm x := by
  unfold torusSpatialNorm
  exact sqrt_nonneg _

theorem torusParabolicSize_nonneg (z : SpaceTime) : 0 ≤ torusParabolicSize z := by
  unfold torusParabolicSize
  exact add_nonneg (sqrt_nonneg _) (torusSpatialNorm_nonneg z.2)

theorem torusSpatialNorm_sq (x : Torus3) :
    torusSpatialNorm x ^ 2 = sqNorm3 (torusCenteredRep x) := by
  unfold torusSpatialNorm
  rw [sq_sqrt]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

theorem torusParabolicSize_eq_time_spatial (z : SpaceTime) :
    torusParabolicSize z = √|z.1| + √(sqNorm3 (torusCenteredRep z.2)) := rfl

end RegularityStructures

end
