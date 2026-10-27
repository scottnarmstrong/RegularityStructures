/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.PastAffineError

/-! Monotonicity of the actual past-ball affine approximation error. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures

 theorem pastAffineError_mono (f : ParabolicSpace → ℝ) (x : ParabolicSpace)
    {r R : ℝ} (hr : r ≤ R) : pastAffineError f x r ≤ pastAffineError f x R := by
  unfold pastAffineError
  apply iInf_mono
  intro c
  apply iInf_mono
  intro ν
  apply iSup_le
  intro y
  apply iSup_le
  intro hy
  exact le_iSup_of_le y (le_iSup_of_le ⟨hy.1.trans_le hr, hy.2⟩ le_rfl)

end GlobalPhi43.Local
