/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.KolmogorovChentsovMoment
public import RegularityStructures.Probability.KolmogorovChentsovScale

/-!
# Close-pair control on the dyadic grid

The five forward neighbours at a dyadic scale control every pair of grid
points whose distance is at most four mesh widths.  This removes the
polynomial loss that is introduced by a general finite pair-reduction lemma.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace RegularityStructures

theorem dyadicGrid_close_le_dyadicCloseSup {E : Type*} [PseudoEMetricSpace E]
    (f : UnitInterval → E) (n : ℕ) {u v : UnitInterval}
    (hu : u ∈ dyadicGridFinset n) (hv : v ∈ dyadicGridFinset n)
    (h : edist u v ≤ ENNReal.ofReal (4 / (2 : ℝ) ^ n)) :
    edist (f u) (f v) ≤ dyadicCloseSup (fun x _ => f x) n () := by
  rcases Finset.mem_image.mp hu with ⟨i, hi, rfl⟩
  rcases Finset.mem_image.mp hv with ⟨j, hj, rfl⟩
  have hreal : dist (dyadicGridPoint n i) (dyadicGridPoint n j) ≤
      4 / (2 : ℝ) ^ n := by
    rw [edist_dist] at h
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
    exact h
  rw [Subtype.dist_eq, Real.dist_eq, dyadicGridPoint_fin_coe,
    dyadicGridPoint_fin_coe] at hreal
  have hdiff : |(i : ℝ) - (j : ℝ)| ≤ 4 := by
    have hinside : (i : ℝ) / (2 : ℝ) ^ n - (j : ℝ) / (2 : ℝ) ^ n =
        ((i : ℝ) - (j : ℝ)) / (2 : ℝ) ^ n := by ring
    have hden : 0 < (2 : ℝ) ^ n := by positivity
    rw [hinside, abs_div, abs_of_pos hden] at hreal
    exact (div_le_div_iff_of_pos_right hden).mp hreal
  by_cases hij : (i : ℕ) ≤ j
  · have hnat : (j : ℕ) - i ≤ 4 := by
      have hsign : (i : ℝ) - (j : ℝ) ≤ 0 := by
        have hcast : (i : ℝ) ≤ j := by exact_mod_cast hij
        linarith
      have hreal' : -((i : ℝ) - (j : ℝ)) ≤ 4 := by
        simpa [abs_of_nonpos hsign] using hdiff
      have hreal'' : (j : ℝ) - i ≤ 4 := by linarith
      have hcast : (j : ℝ) - i = ((j - i : ℕ) : ℝ) := by
        rw [Nat.cast_sub hij]
      rw [hcast] at hreal''
      exact_mod_cast hreal''
    let d : Fin 5 := ⟨(j : ℕ) - i, by omega⟩
    have hneighbor : dyadicNeighbor n i d = j := by
      apply Fin.ext
      change min (i + (d : ℕ)) (2 ^ n) = (j : ℕ)
      dsimp [d]
      rw [Nat.add_sub_of_le hij, min_eq_left]
      exact Nat.le_of_lt_succ j.isLt
    have hsup : edist (f (dyadicGridPoint n i))
        (f (dyadicGridPoint n (dyadicNeighbor n i d))) ≤
        dyadicCloseSup (fun x _ => f x) n () := by
      change _ ≤ ⨆ i : Fin (2 ^ n + 1), ⨆ d : Fin 5,
        edist (f (dyadicGridPoint n i))
          (f (dyadicGridPoint n (dyadicNeighbor n i d)))
      exact le_iSup_of_le i (le_iSup_of_le d le_rfl)
    simpa [hneighbor] using hsup
  · have hji : (j : ℕ) ≤ i := by omega
    have hnat : (i : ℕ) - j ≤ 4 := by
      have hsign : 0 ≤ (i : ℝ) - (j : ℝ) := by
        have hcast : (j : ℝ) ≤ i := by exact_mod_cast hji
        linarith
      have hreal' : (i : ℝ) - (j : ℝ) ≤ 4 := by
        simpa [abs_of_nonneg hsign] using hdiff
      have hcast : (i : ℝ) - j = ((i - j : ℕ) : ℝ) := by
        rw [Nat.cast_sub hji]
      rw [hcast] at hreal'
      exact_mod_cast hreal'
    let d : Fin 5 := ⟨(i : ℕ) - j, by omega⟩
    have hneighbor : dyadicNeighbor n j d = i := by
      apply Fin.ext
      change min (j + (d : ℕ)) (2 ^ n) = (i : ℕ)
      dsimp [d]
      rw [Nat.add_sub_of_le hji, min_eq_left]
      exact Nat.le_of_lt_succ i.isLt
    have hsup : edist (f (dyadicGridPoint n j))
        (f (dyadicGridPoint n (dyadicNeighbor n j d))) ≤
        dyadicCloseSup (fun x _ => f x) n () := by
      change _ ≤ ⨆ i : Fin (2 ^ n + 1), ⨆ d : Fin 5,
        edist (f (dyadicGridPoint n i))
          (f (dyadicGridPoint n (dyadicNeighbor n i d)))
      exact le_iSup_of_le j (le_iSup_of_le d le_rfl)
    rw [edist_comm]
    simpa [hneighbor] using hsup

end RegularityStructures

end
