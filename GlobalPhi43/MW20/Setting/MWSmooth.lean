/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import GlobalPhi43.MW20.Setting.MWKernel
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# `GlobalPhi43.mwSmooth`

The past-looking smoothing `h_T`. Source: MW20 §2.1, in the reflected (past-looking) convention.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace GlobalPhi43

open RegularityStructures

/-- The past-looking smoothing `h_T(x) = ∫ Ψ_T(y − x) h(y) dy` (the reflected, past-looking
convention). -/
def mwSmooth (Φ : ParabolicSpace → ℝ) (T : ℝ) (h : ParabolicSpace → ℝ) (x : ParabolicSpace) : ℝ :=
  ∫ y, mwKernel Φ T (y - x) * h y

end GlobalPhi43

end
