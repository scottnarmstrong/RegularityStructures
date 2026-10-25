/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Theorem512.Sup
public import RegularityStructures.Analysis.Heat.Schauder.Derivative

/-!
# Measurability of derivative-shell pairings in the base point

If `(x, z) ↦ Λ_x(s, z)` is jointly measurable for each `s > 0`, every `Λ_x` is a distribution of
local order `γ` at `x` (uniformly), then `x ↦ ⟨Λ_x, D^k K_n(x − ·)⟩` is measurable: it is the
pointwise limit along `s = 1/(m+1)` of the parametric integrals
`x ↦ ∫ Λ_x(s, z) D^k K_n(x − z) dz`, as in `measurable_pairing_taylorKernel`.  A summable series of
such functions has a measurable sum (`measurable_tsum_of_summable`).

`Model.IsJointMeasurable` is the joint measurability of `(x, z) ↦ (Q_t Π_x e_i)(z)`, the
hypothesis that is needed for the measurability of `x ↦ 𝒦_γ f(x)` (the model of
`RegularityStructures.Abstract.Model` only records measurability on the diagonal).
-/

public section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace RegularityStructures

theorem measurable_tsum_of_summable {α : Type*} [MeasurableSpace α] {u : ℕ → α → ℝ}
    (hu : ∀ n, Measurable (u n)) (hs : ∀ x, Summable fun n => u n x) :
    Measurable fun x => ∑' n, u n x :=
  measurable_of_tendsto_metrizable (f := fun m x => ∑ n ∈ Finset.range m, u n x)
    (fun _ => Finset.measurable_sum _ fun n _ => hu n)
    (tendsto_pi_nhds.2 fun x => (hs x).hasSum.tendsto_sum_nat)

end RegularityStructures

end
