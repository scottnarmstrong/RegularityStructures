/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.Tensorization
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# `L²` closure for conditional means

The product variance estimate is most useful when the conditional means are supplied by the
same `L²` hypothesis as the original function.  These lemmas record that closure explicitly.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace RegularityStructures

theorem memLp_integral_prod_left {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : α × β → ℝ} (hf : MemLp f 2 (μ.prod ν))
    (hfx : ∀ x, MemLp (fun y => f (x, y)) 2 ν) :
    MemLp (fun x => ∫ y, f (x, y) ∂ν) 2 μ := by
  have hfi : Integrable f (μ.prod ν) := hf.integrable (by norm_num)
  have hg : Integrable (fun x => ∫ y, f (x, y) ∂ν) μ := by
    exact hfi.integral_prod_left
  have hfsq : Integrable (fun z => f z ^ 2) (μ.prod ν) := hf.integrable_sq
  have hgsq_bound : Integrable (fun x => ∫ y, f (x, y) ^ 2 ∂ν) μ := by
    exact hfsq.integral_prod_left
  have hgsq : Integrable (fun x => (∫ y, f (x, y) ∂ν) ^ 2) μ := by
    refine hgsq_bound.mono' (hg.aestronglyMeasurable.pow 2) ?_
    filter_upwards [] with x
    have h := integral_sq_le_integral_sq (hfx x)
    have hx : 0 ≤ (∫ y, f (x, y) ∂ν) ^ 2 := sq_nonneg _
    simpa [Real.norm_eq_abs, abs_of_nonneg hx] using h
  exact (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2 hgsq

theorem memLp_integral_prod_right {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : α × β → ℝ} (hf : MemLp f 2 (μ.prod ν))
    (hfy : ∀ y, MemLp (fun x => f (x, y)) 2 μ) :
    MemLp (fun y => ∫ x, f (x, y) ∂μ) 2 ν := by
  have hfi : Integrable f (μ.prod ν) := hf.integrable (by norm_num)
  have hg : Integrable (fun y => ∫ x, f (x, y) ∂μ) ν := by
    exact hfi.integral_prod_right
  have hfsq : Integrable (fun z => f z ^ 2) (μ.prod ν) := hf.integrable_sq
  have hgsq_bound : Integrable (fun y => ∫ x, f (x, y) ^ 2 ∂μ) ν := by
    exact hfsq.integral_prod_right
  have hgsq : Integrable (fun y => (∫ x, f (x, y) ∂μ) ^ 2) ν := by
    refine hgsq_bound.mono' (hg.aestronglyMeasurable.pow 2) ?_
    filter_upwards [] with y
    have h := integral_sq_le_integral_sq (hfy y)
    have hy : 0 ≤ (∫ x, f (x, y) ∂μ) ^ 2 := sq_nonneg _
    simpa [Real.norm_eq_abs, abs_of_nonneg hy] using h
  exact (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2 hgsq

end RegularityStructures

end
