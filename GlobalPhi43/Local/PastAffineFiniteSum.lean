/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.PastAffineSubadditivity

/-! Finite boundary potentials combine at the actual affine infimum. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures
open scoped ENNReal

 theorem pastAffineError_zero_le (x : ParabolicSpace) (R : ℝ) :
    pastAffineError (fun _ => 0) x R ≤ 0 := by
  apply iInf_le_of_le (0 : ℝ)
  apply iInf_le_of_le (0 : Fin 3 → ℝ)
  simp [spatialAffine, spatialLinear]

 theorem pastAffineError_finset_sum_le {I : Type*} (A : Finset I)
    (f : I → ParabolicSpace → ℝ) (x : ParabolicSpace) (R : ℝ) :
    pastAffineError (fun p => ∑ i ∈ A, f i p) x R ≤ ∑ i ∈ A, pastAffineError (f i) x R := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using pastAffineError_zero_le x R
  | @insert i A hi ih =>
    simp only [Finset.sum_insert hi]
    exact (pastAffineError_add_le (f i) (fun p => ∑ j ∈ A, f j p) x R).trans (add_le_add le_rfl ih)

end GlobalPhi43.Local
