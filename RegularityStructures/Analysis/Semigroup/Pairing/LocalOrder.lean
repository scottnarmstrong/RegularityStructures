/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.Pairing.Basic
public import RegularityStructures.Analysis.Semigroup.Operator
public import RegularityStructures.Analysis.Semigroup.OperatorBound

/-!
# Distributions of local order

`IsLocalOrder`: `Λ` is of order `γ` at `x₀` with exponents `A`,
`|Λ_u(y)| ≤ C ∑_{a ∈ A} u^{a/ℓ} d(y, x₀)^{γ - a}` for `0 < u ≤ 1`; `pairing_sub`: the pairing is
additive.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)

/-- `Λ` is of order `γ` at `x₀` with exponents `A`:
`|Λ_u(y)| ≤ C ∑_{a ∈ A} u^{a/ℓ} d(y, x₀)^{γ - a}` for `0 < u ≤ 1`. -/
def IsLocalOrder (Λ : ℝ → E → ℝ) (x₀ : E) (γ : ℝ) (A : Finset ℝ) (C : ℝ) : Prop :=
  ∀ u ∈ Set.Ioc (0 : ℝ) 1, ∀ y,
    |Λ u y| ≤ C * ∑ a ∈ A, u ^ (a / K.order) * K.scaleDist y x₀ ^ (γ - a)

end RegularityStructures.RegularisingSemigroup

end

public section

open MeasureTheory Filter
open scoped Topology

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)

include K in
theorem pairing_sub {Λ Λ' : ℝ → E → ℝ} {φ : E → ℝ} {L L' : ℝ}
    (hi : ∀ s, 0 < s → Integrable (fun y => Λ s y * φ y) μ)
    (hi' : ∀ s, 0 < s → Integrable (fun y => Λ' s y * φ y) μ)
    (h : Tendsto (fun s => ∫ y, Λ s y * φ y ∂μ) (𝓝[>] 0) (𝓝 L))
    (h' : Tendsto (fun s => ∫ y, Λ' s y * φ y ∂μ) (𝓝[>] 0) (𝓝 L')) :
    K.pairing (Λ - Λ') φ = K.pairing Λ φ - K.pairing Λ' φ := by
  rw [K.pairing_eq_of_tendsto h, K.pairing_eq_of_tendsto h']
  refine K.pairing_eq_of_tendsto ((h.sub h').congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Pi.sub_apply, sub_mul]
  rw [integral_sub (hi s hs) (hi' s hs)]

end RegularityStructures.RegularisingSemigroup

end
