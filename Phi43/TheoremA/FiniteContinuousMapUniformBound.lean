/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HolderBesov
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Finite uniform bounds for continuous-map families

Every continuous map on the compact interval `Icc 0 T` has a uniform norm bound.  A finite
induction combines these bounds for the early approximants in the maximal-path construction.
-/

public section

namespace RegularityStructures.Phi43

theorem assembly_finiteContinuousMap_uniformNorm_bound
    {η : NegExponent} {T : ℝ}
    (x : ℕ → C(Set.Icc (0 : ℝ) T, HolderBesov η)) (N : ℕ) :
    ∃ L : ℝ, ∀ n < N, ∀ t : Set.Icc (0 : ℝ) T, ‖x n t‖ ≤ L := by
  induction N with
  | zero =>
      refine ⟨0, ?_⟩
      intro n hn
      exact (Nat.not_lt_zero n hn).elim
  | succ N ih =>
      obtain ⟨Lold, hLold⟩ := ih
      obtain ⟨Lnew, hLnew⟩ :=
        (BoundedContinuousFunction.mkOfCompact (x N)).bddAbove_range_norm_comp
      refine ⟨max Lold Lnew, ?_⟩
      intro n hn t
      by_cases hEq : n = N
      · subst n
        have hmem : ‖BoundedContinuousFunction.mkOfCompact (x N) t‖ ∈
            Set.range (norm ∘ BoundedContinuousFunction.mkOfCompact (x N)) :=
          ⟨t, rfl⟩
        have hnew := hLnew hmem
        change ‖x N t‖ ≤ Lnew at hnew
        exact hnew.trans (le_max_right _ _)
      · have hnle : n ≤ N := Nat.le_of_lt_succ hn
        have hnlt : n < N := lt_of_le_of_ne hnle hEq
        exact (hLold n hnlt t).trans (le_max_left _ _)

end RegularityStructures.Phi43

end
