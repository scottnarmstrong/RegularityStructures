/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.KolmogorovChentsovDyadic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Finite dyadic close-pair controls

At scale `n` only a bounded number of neighbouring grid points can be close.
The definitions here enumerate those neighbours by a finite offset, which is
the counting input for the ENNReal moment estimate.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace RegularityStructures

noncomputable def dyadicNeighbor (n : ℕ) (i : Fin (2 ^ n + 1)) (d : Fin 5) :
    Fin (2 ^ n + 1) :=
  ⟨min ((i : ℕ) + (d : ℕ)) (2 ^ n), by
    exact Nat.lt_succ_of_le
      (min_le_right ((i : ℕ) + (d : ℕ)) (2 ^ n))⟩

theorem dyadicGridPoint_fin_coe (n : ℕ) (i : Fin (2 ^ n + 1)) :
    (dyadicGridPoint n i : ℝ) = (i : ℝ) / (2 : ℝ) ^ n := by
  rw [dyadicGridPoint_coe]
  have hi : (i : ℕ) ≤ 2 ^ n := Nat.le_of_lt_succ i.isLt
  rw [min_eq_left (by exact_mod_cast hi)]

noncomputable def dyadicGridFinset (n : ℕ) : Finset UnitInterval :=
  Finset.univ.image (fun i : Fin (2 ^ n + 1) => dyadicGridPoint n i)

theorem dyadicNeighbor_ge (n : ℕ) (i : Fin (2 ^ n + 1)) (d : Fin 5) :
    (i : ℕ) ≤ (dyadicNeighbor n i d : ℕ) := by
  change (i : ℕ) ≤ min ((i : ℕ) + (d : ℕ)) (2 ^ n)
  apply le_min
  · omega
  · exact Nat.le_of_lt_succ i.isLt

theorem dyadicNeighbor_sub_le (n : ℕ) (i : Fin (2 ^ n + 1)) (d : Fin 5) :
    (dyadicNeighbor n i d : ℕ) - (i : ℕ) ≤ 4 := by
  simp only [dyadicNeighbor]
  have hle : min ((i : ℕ) + (d : ℕ)) (2 ^ n) ≤ (i : ℕ) + 4 := by
    exact (min_le_left _ _).trans (by omega)
  omega

theorem dist_dyadicGridPoint_neighbor_le (n : ℕ) (i : Fin (2 ^ n + 1)) (d : Fin 5) :
    dist (dyadicGridPoint n i) (dyadicGridPoint n (dyadicNeighbor n i d)) ≤
      4 / (2 : ℝ) ^ n := by
  rw [dist_comm, Subtype.dist_eq, Real.dist_eq, abs_of_nonneg]
  · rw [dyadicGridPoint_fin_coe, dyadicGridPoint_fin_coe]
    have hsub : (dyadicNeighbor n i d : ℝ) - (i : ℝ) ≤ 4 := by
      calc
        (dyadicNeighbor n i d : ℝ) - (i : ℝ) =
            (((dyadicNeighbor n i d : ℕ) - (i : ℕ) : ℕ) : ℝ) := by
          rw [Nat.cast_sub (dyadicNeighbor_ge n i d)]
        _ ≤ 4 := by exact_mod_cast dyadicNeighbor_sub_le n i d
    calc
      (dyadicNeighbor n i d : ℝ) / (2 : ℝ) ^ n - (i : ℝ) / (2 : ℝ) ^ n =
          ((dyadicNeighbor n i d : ℝ) - (i : ℝ)) / (2 : ℝ) ^ n := by ring
      _ ≤ 4 / (2 : ℝ) ^ n := div_le_div_of_nonneg_right hsub (by positivity)
  · rw [dyadicGridPoint_fin_coe, dyadicGridPoint_fin_coe]
    apply sub_nonneg.mpr
    exact div_le_div_of_nonneg_right (by exact_mod_cast dyadicNeighbor_ge n i d)
      (by positivity)

end RegularityStructures

end
