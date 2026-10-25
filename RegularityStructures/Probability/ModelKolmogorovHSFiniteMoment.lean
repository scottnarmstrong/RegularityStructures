/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Linear covering costs for finite suprema

The finite-net argument in Hairer--Steele, arXiv:2301.10081v3,
Proposition B.3 uses the p-th moment of a maximum, not the p-th moment
of a sum. Its covering cost is therefore the number of points, without
an extra power depending on p.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace RegularityStructures

/-- The moment of a finite supremum is bounded by the sum of the individual moments. -/
theorem finiteSup_lintegral_pow_le_sum
    {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] {P : Measure Ω}
    {V : I → Ω → ℝ≥0∞} {p : ℕ} (hp : p ≠ 0)
    (hmeas : ∀ i, AEMeasurable (V i) P) :
    ∫⁻ ω, (⨆ i, V i ω) ^ p ∂P ≤ ∑ i, ∫⁻ ω, V i ω ^ p ∂P := by
  have hpoint (ω : Ω) : (⨆ i, V i ω) ^ p ≤ ∑' i, V i ω ^ p := by
    rw [ENNReal.iSup_pow_of_ne_zero hp]
    exact iSup_le fun i => ENNReal.le_tsum (f := fun j => V j ω ^ p) i
  calc
    _ ≤ ∫⁻ ω, ∑' i, V i ω ^ p ∂P := lintegral_mono hpoint
    _ = ∑' i, ∫⁻ ω, V i ω ^ p ∂P := by
      rw [lintegral_tsum (fun i => (hmeas i).pow_const p)]
    _ = _ := tsum_fintype _

/-- Identical pointwise annealed bounds cost only the cardinality of the finite index set. -/
theorem finiteSup_lintegral_pow_le_card_mul
    {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] {P : Measure Ω}
    {V : I → Ω → ℝ≥0∞} {p : ℕ} (hp : p ≠ 0) {B : ℝ≥0∞}
    (hmeas : ∀ i, AEMeasurable (V i) P)
    (hpoint : ∀ i, ∫⁻ ω, V i ω ^ p ∂P ≤ B) :
    ∫⁻ ω, (⨆ i, V i ω) ^ p ∂P ≤ Fintype.card I * B := by
  calc
    _ ≤ ∑ i, ∫⁻ ω, V i ω ^ p ∂P := finiteSup_lintegral_pow_le_sum hp hmeas
    _ ≤ ∑ _i : I, B := Finset.sum_le_sum fun i _ => hpoint i
    _ = _ := by simp

end RegularityStructures

end
