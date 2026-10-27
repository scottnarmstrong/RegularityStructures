/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import GlobalPhi43.MW20.Setting.MWKernel
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# `GlobalPhi43.mwRecenteredSeminorm`

The recentered seminorms `[XV], [A], [B], [D]`. Source: MW20 (2.16)–(2.19).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace GlobalPhi43

open RegularityStructures

/-- The recentered seminorm `sup_{x ∈ C} sup_{0<T<1} T^{-α} |∫ F(x, y) Ψ_T(y − x) dy|` of a two-point integrand
`F(x, y)` (MW20 (2.16)–(2.19), orientation `Ψ_T(y − x)` as printed). For `XV`
the integrand is vector valued and `|·|` is the sup norm of `ℝ³`. -/
def mwRecenteredSeminorm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (Φ : ParabolicSpace → ℝ)
    (α : ℝ) (C : Set ParabolicSpace) (F : ParabolicSpace → ParabolicSpace → E) : ENNReal :=
  ⨆ x ∈ C, ⨆ T ∈ Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (T ^ (-α)) * ‖∫ y, mwKernel Φ T (y - x) • F x y‖ₑ

end GlobalPhi43

end
