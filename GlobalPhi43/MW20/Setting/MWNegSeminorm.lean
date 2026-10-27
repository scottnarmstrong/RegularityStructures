/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import GlobalPhi43.MW20.Setting.MWSmooth
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# `GlobalPhi43.mwNegSeminorm`

The negative local seminorms `[h]_{α,C}`. Source: MW20 (2.9) notation.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace GlobalPhi43

open RegularityStructures

/-- The local negative seminorm `[h]_{α,C} = sup_{0<T≤1} T^{-α} sup_{x ∈ C} |h_T(x)|` (MW20 (2.9) with the
past-looking smoothing), in `[0, ∞]`. -/
def mwNegSeminorm (Φ : ParabolicSpace → ℝ) (α : ℝ) (C : Set ParabolicSpace) (h : ParabolicSpace → ℝ) :
    ENNReal :=
  ⨆ T ∈ Set.Ioc (0 : ℝ) 1, ⨆ x ∈ C, ENNReal.ofReal (T ^ (-α)) * ‖mwSmooth Φ T h x‖ₑ

end GlobalPhi43

end
