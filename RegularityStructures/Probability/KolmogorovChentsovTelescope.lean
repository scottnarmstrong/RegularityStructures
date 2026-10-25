/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.KolmogorovChentsovCore
public import Mathlib.Topology.EMetricSpace.Basic

/-!
# ENNReal telescoping bounds

These lemmas turn eventual equality of a sequence into a bound by the sum of
its successive increments.  They are the deterministic tail estimate used
when dyadic truncations become exactly constant.
-/

@[expose] public section

open Filter Set
open scoped ENNReal NNReal Topology

namespace RegularityStructures

variable {E : Type*} [PseudoEMetricSpace E]

theorem edist_le_tsum_of_eventually_eq {u : ℕ → E} {x : E} {n : ℕ}
    {c : ℕ → ℝ≥0∞}
    (hstep : ∀ k, edist (u k) (u (k + 1)) ≤ c k)
    (heq : ∀ᶠ k in atTop, u k = x) :
    edist (u n) x ≤ ∑' k : ℕ, c k := by
  obtain ⟨m, hm⟩ := eventually_atTop.1 heq
  let m' := max m n
  have hnm : n ≤ m' := le_max_right m n
  have hmx : u m' = x := hm m' (le_max_left m n)
  have hfinite : edist (u n) (u m') ≤
      ∑ k ∈ Finset.Ico n m', edist (u k) (u (k + 1)) :=
    edist_le_Ico_sum_edist u hnm
  rw [hmx] at hfinite
  calc
    edist (u n) x ≤ ∑ k ∈ Finset.Ico n m', edist (u k) (u (k + 1)) := hfinite
    _ ≤ ∑ k ∈ Finset.Ico n m', c k := by
      exact Finset.sum_le_sum fun k hk => hstep k
    _ ≤ ∑' k : ℕ, c k := by
      exact ENNReal.sum_le_tsum (Finset.Ico n m')

end RegularityStructures

end
