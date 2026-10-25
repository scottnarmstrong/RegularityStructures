/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergencePotentialExistence

/-!
# Honest integrability of massive potentials under polynomial growth

The remote past is dominated by its exponential weight. On the remaining bounded time strip the
forcing is bounded and the massive kernel is integrable. This proves integrability at every
observation point before asserting the potential identity, so that the identity is a statement about
genuine integrals. It strengthens the existence component of the convergence of the noise potentials
(`phi43Noise_cauchy`). The kernel is that of equation (2.2) of the statement.
-/

public noncomputable section

open MeasureTheory Real Set

namespace RegularityStructures.Phi43

theorem integrable_massiveHeatKernel_product_of_weighted_past
    {g : SpaceTime → ℝ} (hg : Continuous g)
    (hi : ∀ a : ℝ, IntegrableOn (fun w : SpaceTime => exp w.1 * |g w|)
      {w : SpaceTime | w.1 ≤ a}) (z : SpaceTime) :
    Integrable (fun w : SpaceTime => massiveHeatKernel (z - w) * g w) := by
  let a := z.1 - 2
  let S : Set SpaceTime := {w | a < w.1 ∧ w.1 ≤ z.1}
  have hS : MeasurableSet S :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst measurable_const)
  let g₀ : SpaceTime → ℝ := S.indicator g
  have hg₀ : Measurable g₀ := hg.measurable.indicator hS
  have hcompact : IsCompact (Icc a z.1 ×ˢ (univ : Set Torus3)) :=
    isCompact_Icc.prod isCompact_univ
  obtain ⟨B, hB⟩ := hcompact.bddAbove_image hg.norm.continuousOn
  let D := max B 0
  have hD : 0 ≤ D := le_max_right _ _
  have hg₀B (w : SpaceTime) : ‖g₀ w‖ ≤ D := by
    by_cases hw : w ∈ S
    · rw [show g₀ w = g w from indicator_of_mem hw g]
      exact (hB ⟨w, ⟨⟨hw.1.le, hw.2⟩, mem_univ _⟩, rfl⟩).trans (le_max_left _ _)
    · rw [show g₀ w = 0 from indicator_of_notMem hw g, norm_zero]
      exact hD
  have hlocal : Integrable (fun w : SpaceTime => massiveHeatKernel (z - w) * g₀ w) :=
    (integrable_comp_sub_left_spaceTime integrable_massiveHeatKernel z).mul_bdd
      hg₀.aestronglyMeasurable (Filter.Eventually.of_forall hg₀B)
  have hpast := integrableOn_massiveHeatKernel_past_product hg.measurable (hi a)
    (z := z) (show a + 1 ≤ z.1 by dsimp [a]; linarith)
  have hA : MeasurableSet {w : SpaceTime | w.1 ≤ a} :=
    measurableSet_le measurable_fst measurable_const
  apply ((hpast.integrable_indicator hA).add hlocal).congr
  filter_upwards [] with w
  change {v : SpaceTime | v.1 ≤ a}.indicator
    (fun v => massiveHeatKernel (z - v) * g v) w +
      massiveHeatKernel (z - w) * g₀ w = massiveHeatKernel (z - w) * g w
  by_cases hw : w.1 ≤ a
  · have hnS : w ∉ S := fun h => (not_lt_of_ge hw) h.1
    rw [indicator_of_mem (show w ∈ {v : SpaceTime | v.1 ≤ a} from hw),
      show g₀ w = 0 from indicator_of_notMem hnS g, mul_zero, add_zero]
  · rw [indicator_of_notMem (show w ∉ {v : SpaceTime | v.1 ≤ a} from hw), zero_add]
    by_cases hwS : w ∈ S
    · rw [show g₀ w = g w from indicator_of_mem hwS g]
    · have hfuture : z.1 < w.1 := by
        by_contra hh
        exact hwS ⟨lt_of_not_ge hw, le_of_not_gt hh⟩
      have htime : ¬0 < (z - w).1 := by
        change ¬0 < z.1 - w.1
        linarith only [hfuture]
      have hzero : massiveHeatKernel (z - w) = 0 := by
        simp only [massiveHeatKernel, htime, ↓reduceIte]
      rw [hzero, zero_mul, zero_mul]

end RegularityStructures.Phi43

end

