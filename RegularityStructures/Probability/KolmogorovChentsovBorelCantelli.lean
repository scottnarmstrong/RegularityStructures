/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# ENNReal tails and Borel–Cantelli for dyadic controls

This module packages the measure-theoretic tail step in the
Kolmogorov–Chentsov proof.  Markov's inequality is kept in its native
multiplied ENNReal form, and first Borel–Cantelli supplies the eventual bound.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem ae_eventually_lt_of_summable_level_measure {F : ℕ → Ω → ℝ≥0∞}
    {ε : ℕ → ℝ≥0∞}
    (hlevel : ∑' n, P {ω | ε n ≤ F n ω} ≠ ∞) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, F n ω < ε n := by
  have hnot : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∉ {ω | ε n ≤ F n ω} :=
    ae_eventually_notMem hlevel
  filter_upwards [hnot] with ω hω
  filter_upwards [hω] with n hn
  exact lt_of_not_ge (by simpa only [Set.mem_ofPred_eq] using hn)

theorem ae_eventually_lt_of_summable_level_bound {F : ℕ → Ω → ℝ≥0∞}
    {ε b : ℕ → ℝ≥0∞}
    (hb : ∀ n, P {ω | ε n ≤ F n ω} ≤ b n)
    (hbsum : ∑' n, b n ≠ ∞) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, F n ω < ε n := by
  apply ae_eventually_lt_of_summable_level_measure
  exact (lt_of_le_of_lt (ENNReal.tsum_le_tsum fun n => hb n)
    (lt_top_iff_ne_top.mpr hbsum)).ne

end RegularityStructures

end
