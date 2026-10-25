/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Heat.Kernel
public import Phi43.Potential.TailLattice

/-!
# Local integrability of the heat kernel on `ℝ × ℝ³`

`heatKernelR4` truncated to lags `< a` is integrable (`integrable_heatKernelR4_lag`): its spatial
integral is `1` for `0 < t`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures.Potential

theorem integrable_heatKernelR4_lag (a : ℝ) :
    Integrable (fun w : ParabolicSpace => if w.1 < a then heatKernelR4 w else 0) := by
  have hm : Measurable (fun w : ParabolicSpace => if w.1 < a then heatKernelR4 w else 0) :=
    Measurable.ite (measurableSet_lt measurable_fst measurable_const) measurable_heatKernelR4
      measurable_const
  rw [Measure.volume_eq_prod]
  refine (integrable_prod_iff hm.aestronglyMeasurable).2 ⟨?_, ?_⟩
  · refine Filter.Eventually.of_forall fun t => ?_
    by_cases h0 : 0 < t
    · by_cases ha : t < a
      · simpa [ha, heatKernelR4, h0] using integrable_gaussKernel h0
      · simp [ha]
    · have : ∀ x : Fin 3 → ℝ, (if (t, x).1 < a then heatKernelR4 (t, x) else 0) = 0 := by
        intro x
        split_ifs <;> simp [heatKernelR4_of_nonpos (z := (t, x)) (not_lt.1 h0)]
      simp only [this]
      exact integrable_zero _ _ _
  · have e : (fun t : ℝ => ∫ x : Fin 3 → ℝ, ‖(if (t, x).1 < a then heatKernelR4 (t, x) else 0)‖) =
        (Ioo 0 a).indicator (fun _ => (1 : ℝ)) := by
      funext t
      by_cases h0 : 0 < t
      · by_cases ha : t < a
        · rw [indicator_of_mem (show t ∈ Ioo 0 a from ⟨h0, ha⟩)]
          simp only [ha, ite_true, Real.norm_of_nonneg (heatKernelR4_nonneg _)]
          exact integral_heatKernelR4_slice h0
        · rw [indicator_of_notMem (show t ∉ Ioo 0 a from fun h => ha h.2)]
          simp [ha]
      · rw [indicator_of_notMem (show t ∉ Ioo 0 a from fun h => h0 h.1)]
        have : ∀ x : Fin 3 → ℝ, (if (t, x).1 < a then heatKernelR4 (t, x) else 0) = 0 := by
          intro x
          split_ifs <;> simp [heatKernelR4_of_nonpos (z := (t, x)) (not_lt.1 h0)]
        simp [this]
    rw [e, integrable_indicator_iff measurableSet_Ioo]
    exact integrableOn_const (by simp)

end RegularityStructures.Potential

end
