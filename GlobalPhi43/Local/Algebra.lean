/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Tactic.Ring
public import Mathlib.Basic.Real.Basic

/-! Pointwise algebra for the local two-point expansion. These identities do not
supply the analytic heat-operator linearity or the local PDE hypotheses. -/
public section

namespace GlobalPhi43.Local

/-- The local two-point expansion, with `v = u - J`. -/
@[expose] def expansion {E : Type*} (v Y Z : E → ℝ) (x y : E) : ℝ :=
  v y - v x + Z y - Z x + 3 * v x * (Y y - Y x)

/-- Defining equation exported for consumers of the shared local expansion.
The definition itself need not be unfolded across the module boundary. -/
theorem expansion_eq {E : Type*} (v Y Z : E → ℝ) (x y : E) :
    expansion v Y Z x y = v y - v x + Z y - Z x + 3 * v x * (Y y - Y x) := rfl

/-- The three-point identity has no defect contribution. -/
theorem expansion_three_point {E : Type*} (v Y Z : E → ℝ) (x y z : E) :
    expansion v Y Z x z - expansion v Y Z x y - expansion v Y Z y z =
      -3 * (v y - v x) * (Y z - Y y) := by
  unfold expansion
  ring

/-- The diagonal normalization required by the Schauder lemma. -/
theorem expansion_diag {E : Type*} (v Y Z : E → ℝ) (x : E) :
    expansion v Y Z x x = 0 := by
  unfold expansion
  ring

end GlobalPhi43.Local
