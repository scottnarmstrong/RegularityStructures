/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import GlobalPhi43.MW20.Setting.PastBall
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# `GlobalPhi43.IsMWTestKernel`

The admissible MW20 test kernels `Φ`. Source: MW20 §2.1.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace GlobalPhi43

open RegularityStructures

/-- `Φ` is an admissible MW20 test kernel: smooth, supported in the past ball `B(0, 1)` (closed support inside
it), with `0 ≤ Φ ≤ 1`, `∫ Φ = 1`, and spatially even (MW20 §2.1). -/
def IsMWTestKernel (Φ : ParabolicSpace → ℝ) : Prop :=
  ContDiff ℝ ∞ Φ ∧ tsupport Φ ⊆ pastBall 0 1 ∧ (∀ z, 0 ≤ Φ z ∧ Φ z ≤ 1) ∧
    ∫ z, Φ z = 1 ∧ ∀ z : ParabolicSpace, Φ (z.1, -z.2) = Φ z

end GlobalPhi43

end
