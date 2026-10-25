/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Uniqueness

/-!
# Uniqueness of the limit

Conditions (A1)–(A3) of Theorem A determine the limit. Two pairs `(τ, v)` and `(τ', v')` that
satisfy them for the same solutions have almost surely equal explosion times, and almost surely
equal paths before that time. So condition (A4), mollifier independence, compares well-defined
objects. The proof needs only monotonicity and subadditivity of the probability.

The proof is `RegularityStructures.Phi43.IsPhi43Limit.unique`,
in the module `Phi43.Uniqueness`.

Source: the statement, Proposition 3.1.
-/

public section

namespace RegularityStructures.Phi43.Statements

open MeasureTheory
open scoped ENNReal

/-- **Proposition 3.1.** Conditions (A1)–(A3) determine the limit: two limits of the same
solutions have almost surely equal explosion times and almost surely equal paths before them. -/
theorem proposition31 :
    ∀ {Ω : Type*} {η : NegExponent} {u₀ : C(Torus3, ℝ)} {u : ℝ → Ω → ℝ → C(Torus3, ℝ)}
      {τ τ' : Ω → ℝ≥0∞} {v v' : Ω → ℝ → HolderBesov η} [MeasurableSpace Ω] {P : Measure Ω},
      IsPhi43Limit P η u₀ u τ v → IsPhi43Limit P η u₀ u τ' v' →
        τ =ᵐ[P] τ' ∧ ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → ENNReal.ofReal t < τ ω → v ω t = v' ω t :=
  by exact RegularityStructures.Phi43.IsPhi43Limit.unique

end RegularityStructures.Phi43.Statements

end
