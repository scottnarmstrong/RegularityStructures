/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Growth.Analysis.Linear
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup
import RegularityStructures.Analysis.Heat.Schauder.TaylorPairing

/-!
# Distributions of local order with growth above `-2`

`KRegularG Λ x` records that `Λ` is a measurable `Q`-family of local order `α` at `x` with
polynomial growth `q ≥ 0` and exponents in `(-2, α]` (the situation of `Π_x e_i` under weighted
bounds). For such `Λ` the convolution `K ∗ Λ = ∑_n ⟨Λ, K_n(z - ·)⟩` is a function of polynomial
growth; this is proved for a general shell profile in
`RegularityStructures.Abstract.Profile.Growth.KConv`. Input of [Hai14, Lemma 5.16].
-/

public section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace RegularityStructures

/-- `Λ` is a measurable `Q`-family of local order `α` at `x` with growth `q ≥ 0` and exponents in
`(-2, α]`. -/
@[expose] def KRegularG (Λ : ℝ → ParabolicSpace → ℝ) (x : ParabolicSpace) : Prop :=
  Λ ∈ parabolicSemigroup.distributions ∧ (∀ u, 0 < u → Measurable (Λ u)) ∧
    ∃ (α C q : ℝ) (A : Finset ℝ), (∀ a ∈ A, -2 < a ∧ a ≤ α) ∧ 0 ≤ C ∧ 0 ≤ q ∧
      parabolicSemigroup.IsLocalOrderGrowth Λ x α A C q

end RegularityStructures

end
