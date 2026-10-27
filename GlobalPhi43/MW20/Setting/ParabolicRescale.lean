/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.Basic

/-!
# `GlobalPhi43.parabolicRescale`

Parabolic rescaling `T^{-5} φ(S_T^{-1} ·)`. Source: MW20 §2.1.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace GlobalPhi43

open RegularityStructures

/-- The parabolic rescaling `φ_T(t, x) = T⁻⁵ φ(t/T², x/T)` (MW20 `Φ_T`; the scaled test is
`φ^T_x(y) = φ_T(y − x)`). -/
def parabolicRescale (φ : ParabolicSpace → ℝ) (T : ℝ) (z : ParabolicSpace) : ℝ :=
  T ^ (-5 : ℤ) * φ (z.1 / T ^ 2, T⁻¹ • z.2)

end GlobalPhi43

end
