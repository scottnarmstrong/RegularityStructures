/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Normed.Group.Basic

/-!
# `GlobalPhi43.c4Norm`

The `C⁴` norm `‖φ‖_{C⁴}` of a test function.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace GlobalPhi43

open RegularityStructures

/-- The `C⁴` norm `‖φ‖_{C⁴} = max_{k ≤ 4} sup_z ‖D^k φ(z)‖`, in `[0, ∞]`. -/
def c4Norm (φ : ParabolicSpace → ℝ) : ENNReal :=
  ⨆ k ∈ Finset.range 5, ⨆ z, ‖iteratedFDeriv ℝ k φ z‖ₑ

end GlobalPhi43

end
