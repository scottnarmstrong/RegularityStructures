/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Model
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Annealed closure of local model norms

This is the finite-sector closure step in Hairer [Hai14, Proposition 3.32 and Theorem 10.7].
The random Q-family/Kolmogorov layer supplies random nonnegative constants for the `Π` and `Γ`
bounds.  Since the basis is finite, the deterministic norm characterisations on `Model` turn
those constants into a local model norm, and the elementary inequality
`(a + b)^p ≤ 2^(p-1) (a^p + b^p)` gives its moment.

The theorem is stated on an arbitrary set `S`; taking `S` to be a compact parabolic set gives the
usual local model norm.  Measurability of the two random constants is explicit.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace RegularityStructures

/-!
The infimum definitions for differences are kept here because the deterministic model API has
separate predicates for differences of `Π` and `Γ`.
-/

namespace Model

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : Type*} [MeasurableSpace E] {μ : Measure E}
  {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ}

/-- The `Π` difference norm on a set, dual to `Model.piNormOn`. -/
def piDiffNormOn (M₁ M₂ : Model 𝒯 K) (γ : ℝ) (S : Set E) : ℝ≥0∞ :=
  ⨅ (C : ℝ≥0) (_ : M₁.PiDiffBoundOn M₂ γ C S), (C : ℝ≥0∞)

/-- The `Γ` difference norm on a set, dual to `Model.gammaNormOn`. -/
def gammaDiffNormOn (M₁ M₂ : Model 𝒯 K) (γ : ℝ) (S : Set E) : ℝ≥0∞ :=
  ⨅ (C : ℝ≥0) (_ : M₁.GammaDiffBoundOn M₂ γ C S), (C : ℝ≥0∞)

/-- The local norm of the difference of two models. -/
def diffNormOn (M₁ M₂ : Model 𝒯 K) (γ : ℝ) (S : Set E) : ℝ≥0∞ :=
  M₁.piDiffNormOn M₂ γ S + M₁.gammaDiffNormOn M₂ γ S

end Model

end RegularityStructures

end
