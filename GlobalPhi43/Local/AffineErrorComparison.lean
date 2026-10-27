/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.PastAffineError

/-! Smoothing comparisons act directly on the actual affine infimum,
including infinite values; no minimizer is assumed. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures
open scoped ENNReal

/-- Uniformly close functions have uniformly close best affine errors. -/
theorem pastAffineError_le_of_close (f g : ParabolicSpace → ℝ) (x : ParabolicSpace)
    {R E : ℝ} (hclose : ∀ y ∈ pastBall x R, |f y - g y| ≤ E) :
    pastAffineError f x R ≤ pastAffineError g x R + ENNReal.ofReal E := by
  have hc (c : ℝ) (ν : Fin 3 → ℝ) :
      (⨆ y ∈ pastBall x R, ENNReal.ofReal |f y - spatialAffine x c ν y|) ≤
        (⨆ y ∈ pastBall x R, ENNReal.ofReal |g y - spatialAffine x c ν y|) + ENNReal.ofReal E := by
    have hg : ∀ y ∈ pastBall x R, ENNReal.ofReal |g y - spatialAffine x c ν y| ≤
        (⨆ z ∈ pastBall x R, ENNReal.ofReal |g z - spatialAffine x c ν z|) := by
      simpa only [iSup_le_iff] using
        (le_rfl : (⨆ z ∈ pastBall x R, ENNReal.ofReal |g z - spatialAffine x c ν z|) ≤
          (⨆ z ∈ pastBall x R, ENNReal.ofReal |g z - spatialAffine x c ν z|))
    apply iSup_le
    intro y
    apply iSup_le
    intro hy
    have habs : |f y - spatialAffine x c ν y| ≤ |g y - spatialAffine x c ν y| + E := by
      calc
        _ = |(g y - spatialAffine x c ν y) + (f y - g y)| := by congr 1; ring
        _ ≤ |g y - spatialAffine x c ν y| + |f y - g y| := abs_add_le _ _
        _ ≤ _ := add_le_add le_rfl (hclose y hy)
    calc
      _ ≤ ENNReal.ofReal (|g y - spatialAffine x c ν y| + E) := ENNReal.ofReal_le_ofReal habs
      _ ≤ ENNReal.ofReal |g y - spatialAffine x c ν y| + ENNReal.ofReal E := ENNReal.ofReal_add_le
      _ ≤ _ := add_le_add (hg y hy) le_rfl
  unfold pastAffineError
  simp_rw [ENNReal.iInf_add]
  apply le_iInf
  intro c
  apply le_iInf
  intro ν
  exact iInf_le_of_le c (iInf_le_of_le ν (hc c ν))

end GlobalPhi43.Local
