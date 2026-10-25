/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.KolmogorovChentsovBorelCantelli
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Order.CompletePartialOrder

/-!
# ENNReal supremum moment bookkeeping

The scale variables in the Kolmogorov--Chentsov construction are extended
nonnegative-real-valued.  This lemma bounds their supremum by the sum of their
individual p-moments, with no hidden integrability assumption.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal Topology

namespace RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem lintegral_iSup_pow_le_tsum_lintegral_pow {p : ℕ} (hp : 1 ≤ p)
    {Y : ℕ → Ω → ℝ≥0∞}
    (hmeas : ∀ n, AEMeasurable (Y n) P) :
    ∫⁻ ω, (⨆ n, Y n ω) ^ p ∂P ≤
      ∑' n, ∫⁻ ω, (Y n ω) ^ p ∂P := by
  have hp0 : p ≠ 0 := by omega
  have hpoint : ∀ ω, (⨆ n, Y n ω) ^ p ≤ ∑' n, (Y n ω) ^ p := by
    intro ω
    rw [ENNReal.iSup_pow_of_ne_zero hp0]
    exact iSup_le fun n => ENNReal.le_tsum (f := fun m => (Y m ω) ^ p) n
  calc
    ∫⁻ ω, (⨆ n, Y n ω) ^ p ∂P ≤ ∫⁻ ω, ∑' n, (Y n ω) ^ p ∂P :=
      lintegral_mono hpoint
    _ = ∑' n, ∫⁻ ω, (Y n ω) ^ p ∂P := by
      rw [lintegral_tsum]
      intro n
      exact (hmeas n).pow_const p

end RegularityStructures

end
