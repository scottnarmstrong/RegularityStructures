/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.PastAffineError

/-! The actual affine infimum is subadditive, including infinite values.
No affine minimizer is assumed or selected. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures
open scoped ENNReal

 theorem pastAffineError_add_le (f g : ParabolicSpace → ℝ) (x : ParabolicSpace) (R : ℝ) :
    pastAffineError (fun y => f y + g y) x R ≤ pastAffineError f x R + pastAffineError g x R := by
  unfold pastAffineError
  simp_rw [ENNReal.iInf_add, ENNReal.add_iInf]
  apply le_iInf
  intro cf
  apply le_iInf
  intro νf
  apply le_iInf
  intro cg
  apply le_iInf
  intro νg
  apply iInf_le_of_le (cf + cg)
  apply iInf_le_of_le (νf + νg)
  apply iSup_le
  intro y
  apply iSup_le
  intro hy
  have hf : ENNReal.ofReal |f y - spatialAffine x cf νf y| ≤
      ⨆ z ∈ pastBall x R, ENNReal.ofReal |f z - spatialAffine x cf νf z| :=
    le_iSup_of_le y (le_iSup_of_le hy le_rfl)
  have hg : ENNReal.ofReal |g y - spatialAffine x cg νg y| ≤
      ⨆ z ∈ pastBall x R, ENNReal.ofReal |g z - spatialAffine x cg νg z| :=
    le_iSup_of_le y (le_iSup_of_le hy le_rfl)
  have ha : spatialAffine x (cf + cg) (νf + νg) y = spatialAffine x cf νf y + spatialAffine x cg νg y := by
    simp only [spatialAffine, spatialLinear, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  have habs : |f y + g y - spatialAffine x (cf + cg) (νf + νg) y| ≤
      |f y - spatialAffine x cf νf y| + |g y - spatialAffine x cg νg y| := by
    rw [ha]
    calc
      |f y + g y - (spatialAffine x cf νf y + spatialAffine x cg νg y)| =
          |(f y - spatialAffine x cf νf y) + (g y - spatialAffine x cg νg y)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  exact (ENNReal.ofReal_le_ofReal habs).trans (ENNReal.ofReal_add_le.trans (add_le_add hf hg))

end GlobalPhi43.Local
