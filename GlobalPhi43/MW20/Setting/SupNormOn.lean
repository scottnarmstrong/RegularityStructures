/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.Basic
public import Mathlib.Analysis.Normed.Group.Basic

/-!
# `GlobalPhi43.supNormOn`

The sup norm on a set. Source: MW20 (2.4).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace GlobalPhi43

open RegularityStructures

/-- The sup norm `‖f‖_C = sup_{z ∈ C} |f(z)|` (MW20 (2.4)), in `[0, ∞]`. -/
def supNormOn (C : Set ParabolicSpace) (f : ParabolicSpace → ℝ) : ENNReal :=
  ⨆ z ∈ C, ‖f z‖ₑ

end GlobalPhi43

end
