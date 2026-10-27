/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import GlobalPhi43.MW20.Setting.ParabolicDist
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# `GlobalPhi43.parabolicHolderSeminorm`

The positive local Hölder seminorms. Source: MW20 (2.4), restricted notation.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace GlobalPhi43

open RegularityStructures

/-- The local Hölder seminorm `[f]_{α,C} = sup_{z ≠ w ∈ C} |f(z) − f(w)| / d(z, w)^α` (MW20 (2.4), local version),
in `[0, ∞]`. -/
def parabolicHolderSeminorm (α : ℝ) (C : Set ParabolicSpace) (f : ParabolicSpace → ℝ) : ENNReal :=
  ⨆ z ∈ C, ⨆ w ∈ C, ⨆ (_ : z ≠ w), ENNReal.ofReal (|f z - f w| / parabolicDist z w ^ α)

end GlobalPhi43

end
