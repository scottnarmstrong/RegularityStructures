/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.KolmogorovChentsovScale
public import RegularityStructures.Probability.KolmogorovChentsovTelescope
public import RegularityStructures.Probability.KolmogorovChentsovFinite

/-!
# Dyadic approximation facts

These are the elementary approximation estimates used to pass from
scale-wise grid bounds to a Hölder estimate on the dense dyadic skeleton.
-/

@[expose] public section

open Filter Set
open scoped ENNReal NNReal Topology

namespace RegularityStructures

theorem dyadicApprox_mem_gridFinset (n : ℕ) (x : UnitInterval) :
    dyadicApprox n x ∈ dyadicGridFinset n := by
  let k : Fin (2 ^ n + 1) :=
    ⟨Nat.floor ((x : ℝ) * (2 : ℝ) ^ n), by
      exact Nat.lt_succ_of_le (nat_floor_mul_pow_le n x)⟩
  refine Finset.mem_image.2 ⟨k, Finset.mem_univ _, ?_⟩
  simp [dyadicApprox, k]

theorem dyadicApprox_eq_finer (n : ℕ) (x : UnitInterval) :
    dyadicApprox (n + 1) (dyadicApprox n x) = dyadicApprox n x := by
  let k : ℕ := Nat.floor ((x : ℝ) * (2 : ℝ) ^ n)
  change dyadicApprox (n + 1) (dyadicGridPoint n k) = dyadicGridPoint n k
  exact dyadicApprox_eq_gridPoint_of_le (k := k) (by omega)

theorem dyadicApprox_mem_finer_gridFinset (n : ℕ) (x : UnitInterval) :
    dyadicApprox n x ∈ dyadicGridFinset (n + 1) := by
  rw [← dyadicApprox_eq_finer n x]
  exact dyadicApprox_mem_gridFinset (n + 1) (dyadicApprox n x)

theorem dist_dyadicApprox_succ_le (n : ℕ) (x : UnitInterval) :
    dist (dyadicApprox n x) (dyadicApprox (n + 1) x) ≤
      4 / (2 : ℝ) ^ (n + 1) := by
  have hstep : dist (dyadicApprox n x) (dyadicApprox (n + 1) x) ≤
      1 / (2 : ℝ) ^ n + 1 / (2 : ℝ) ^ (n + 1) := by
    calc
      dist (dyadicApprox n x) (dyadicApprox (n + 1) x) ≤
          dist (dyadicApprox n x) x + dist x (dyadicApprox (n + 1) x) :=
        dist_triangle _ _ _
      _ ≤ 1 / (2 : ℝ) ^ n + 1 / (2 : ℝ) ^ (n + 1) :=
        add_le_add (by simpa [dist_comm] using dist_dyadicApprox_le n x)
          (dist_dyadicApprox_le (n + 1) x)
  calc
    dist (dyadicApprox n x) (dyadicApprox (n + 1) x) ≤
        1 / (2 : ℝ) ^ n + 1 / (2 : ℝ) ^ (n + 1) := hstep
    _ = 3 / (2 : ℝ) ^ (n + 1) := by
      field_simp
      ring
    _ ≤ 4 / (2 : ℝ) ^ (n + 1) := by
      gcongr
      norm_num

theorem edist_dyadicApprox_succ_le (n : ℕ) (x : UnitInterval) :
    edist (dyadicApprox n x) (dyadicApprox (n + 1) x) ≤
      ENNReal.ofReal (4 / (2 : ℝ) ^ (n + 1)) := by
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal (dist_dyadicApprox_succ_le n x)

end RegularityStructures

end
