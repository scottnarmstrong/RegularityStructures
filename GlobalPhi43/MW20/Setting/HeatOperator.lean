/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# `GlobalPhi43.heatOperator`

The heat operator `L = ∂_t − Δ`. Source: MW20 §2.1.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace GlobalPhi43

open RegularityStructures

/-- The heat operator `(L f)(z) = ∂_t f(z) − Σ_i ∂²_{x_i} f(z)` on `ℝ × ℝ³`, by Fréchet derivatives (MW20 §2.1). -/
def heatOperator (f : ParabolicSpace → ℝ) (z : ParabolicSpace) : ℝ :=
  fderiv ℝ f z (1, 0) -
    ∑ i : Fin 3, fderiv ℝ (fun w => fderiv ℝ f w (0, Pi.single i 1)) z (0, Pi.single i 1)

end GlobalPhi43

end
