/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Topology.MetricSpace.Basic

/-!
# Dyadic approximation on the unit interval

This file records the elementary dyadic geometry used in the
Kolmogorov--Chentsov construction.  The truncation map is defined by the
natural floor, so it is compatible with the dyadic skeleton without choosing
representatives of dyadic rationals.
-/

@[expose] public section

open Filter Set
open scoped ENNReal NNReal Topology

namespace RegularityStructures

abbrev UnitInterval := Set.Icc (0 : ℝ) 1

noncomputable def dyadicGridPoint (n k : ℕ) : UnitInterval :=
  ⟨(min k (2 ^ n) : ℝ) / (2 : ℝ) ^ n, by
    constructor
    · exact div_nonneg (by positivity) (by positivity)
    · apply (div_le_iff₀ (by positivity)).2
      have h : (min k (2 ^ n) : ℝ) ≤ (2 ^ n : ℝ) := by
        exact_mod_cast Nat.min_le_right k (2 ^ n)
      simpa only [one_mul, ← Nat.cast_pow] using
        h
  ⟩

noncomputable def dyadicApprox (n : ℕ) (x : UnitInterval) : UnitInterval :=
  dyadicGridPoint n (Nat.floor ((x : ℝ) * (2 : ℝ) ^ n))

noncomputable def dyadicUnitSet : Set UnitInterval :=
  ⋃ n : ℕ, Set.range (fun k : Fin (2 ^ n + 1) => dyadicGridPoint n k)

theorem dyadicGridPoint_coe (n k : ℕ) :
    (dyadicGridPoint n k : ℝ) = (min k (2 ^ n) : ℝ) / (2 : ℝ) ^ n :=
  rfl

theorem nat_floor_mul_pow_le (n : ℕ) (x : UnitInterval) :
    Nat.floor ((x : ℝ) * (2 : ℝ) ^ n) ≤ 2 ^ n := by
  apply Nat.floor_le_of_le
  calc
    (x : ℝ) * (2 : ℝ) ^ n ≤ 1 * (2 : ℝ) ^ n :=
      mul_le_mul_of_nonneg_right x.2.2 (by positivity)
    _ = (2 ^ n : ℕ) := by
      convert (Nat.cast_pow 2 n (α := ℝ)).symm using 1
      norm_num

theorem dyadicApprox_coe (n : ℕ) (x : UnitInterval) :
    (dyadicApprox n x : ℝ) =
      (Nat.floor ((x : ℝ) * (2 : ℝ) ^ n) : ℝ) / (2 : ℝ) ^ n := by
  change (min (Nat.floor ((x : ℝ) * (2 : ℝ) ^ n)) (2 ^ n) : ℝ) /
      (2 : ℝ) ^ n = _
  have h : (Nat.floor ((x : ℝ) * (2 : ℝ) ^ n) : ℝ) ≤ (2 ^ n : ℝ) := by
    exact_mod_cast nat_floor_mul_pow_le n x
  rw [min_eq_left h]

theorem dyadicApprox_le (n : ℕ) (x : UnitInterval) :
    (dyadicApprox n x : ℝ) ≤ x := by
  rw [dyadicApprox_coe]
  apply (div_le_iff₀ (by positivity)).2
  exact Nat.floor_le (mul_nonneg x.2.1 (by positivity))

theorem lt_dyadicApprox_add (n : ℕ) (x : UnitInterval) :
    (x : ℝ) < (dyadicApprox n x : ℝ) + 1 / (2 : ℝ) ^ n := by
  have hfloor := Nat.lt_floor_add_one ((x : ℝ) * (2 : ℝ) ^ n)
  have hpow : 0 < (2 : ℝ) ^ n := by positivity
  calc
    (x : ℝ) = ((x : ℝ) * (2 : ℝ) ^ n) / (2 : ℝ) ^ n := by
      field_simp
    _ < ((Nat.floor ((x : ℝ) * (2 : ℝ) ^ n) : ℝ) + 1) /
        (2 : ℝ) ^ n := (div_lt_div_of_pos_right hfloor hpow)
    _ = (dyadicApprox n x : ℝ) + 1 / (2 : ℝ) ^ n := by
      rw [dyadicApprox_coe]
      ring

theorem edist_dyadicApprox_le (n : ℕ) (x : UnitInterval) :
    edist (x : ℝ) (dyadicApprox n x) ≤ ENNReal.ofReal (1 / (2 : ℝ) ^ n) := by
  rw [edist_dist, Real.dist_eq]
  apply ENNReal.ofReal_le_ofReal
  rw [abs_of_nonneg]
  · exact le_of_lt ((sub_lt_iff_lt_add').2 (lt_dyadicApprox_add n x))
  · exact sub_nonneg.mpr (dyadicApprox_le n x)

theorem dist_dyadicApprox_le (n : ℕ) (x : UnitInterval) :
    dist x (dyadicApprox n x) ≤ 1 / (2 : ℝ) ^ n := by
  rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg]
  · exact le_of_lt ((sub_lt_iff_lt_add').2 (lt_dyadicApprox_add n x))
  · exact sub_nonneg.mpr (dyadicApprox_le n x)

theorem dyadicApprox_mem (n : ℕ) (x : UnitInterval) :
    dyadicApprox n x ∈ dyadicUnitSet := by
  let k : Fin (2 ^ n + 1) :=
    ⟨Nat.floor ((x : ℝ) * (2 : ℝ) ^ n), by
      exact Nat.lt_succ_of_le (nat_floor_mul_pow_le n x)⟩
  refine mem_iUnion.2 ⟨n, ⟨k, ?_⟩⟩
  simp [dyadicApprox, k]

theorem dense_dyadicUnitSet : Dense dyadicUnitSet := by
  rw [Metric.dense_iff]
  intro x r hr
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨dyadicApprox n x, ?_, dyadicApprox_mem n x⟩
  rw [Metric.mem_ball]
  simpa [dist_comm] using (dist_dyadicApprox_le n x).trans_lt (by
    simpa [one_div, div_pow] using hn)

theorem dyadicApprox_eq_gridPoint_of_le {m n k : ℕ} (hmn : m ≤ n) :
    dyadicApprox n (dyadicGridPoint m k) = dyadicGridPoint m k := by
  let j := min k (2 ^ m)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have hj : j ≤ 2 ^ m := Nat.min_le_right k (2 ^ m)
  have hpow : (2 : ℝ) ^ (m + d) = (2 : ℝ) ^ m * (2 : ℝ) ^ d := by
    rw [pow_add]
  have hmin : ((min k (2 ^ m) : ℕ) : ℝ) =
      min (k : ℝ) ((2 : ℝ) ^ m) := by
    rw [Nat.cast_min, Nat.cast_pow]
    norm_num
  have hmul : (j : ℝ) * (2 : ℝ) ^ d = (j * 2 ^ d : ℕ) := by
    rw [Nat.cast_mul, Nat.cast_pow]
    norm_num
  have harg : ((dyadicGridPoint m k : ℝ) * (2 : ℝ) ^ (m + d)) =
      (j * 2 ^ d : ℕ) := by
    calc
      (dyadicGridPoint m k : ℝ) * (2 : ℝ) ^ (m + d) =
          min (k : ℝ) ((2 : ℝ) ^ m) / (2 : ℝ) ^ m *
            ((2 : ℝ) ^ m * (2 : ℝ) ^ d) := by
        rw [dyadicGridPoint_coe, hpow]
      _ = min (k : ℝ) ((2 : ℝ) ^ m) * (2 : ℝ) ^ d := by
        field_simp
      _ = (j : ℝ) * (2 : ℝ) ^ d := by
        rw [← hmin]
      _ = (j * 2 ^ d : ℕ) := hmul
  have hfloor : Nat.floor ((dyadicGridPoint m k : ℝ) * (2 : ℝ) ^ (m + d)) =
      j * 2 ^ d := by
    rw [harg]
    exact Nat.floor_natCast _
  change dyadicGridPoint (m + d)
      (Nat.floor ((dyadicGridPoint m k : ℝ) * (2 : ℝ) ^ (m + d))) =
    dyadicGridPoint m k
  apply Subtype.ext
  change (min (Nat.floor ((dyadicGridPoint m k : ℝ) * (2 : ℝ) ^ (m + d)) : ℝ)
      ((2 : ℝ) ^ (m + d))) / (2 : ℝ) ^ (m + d) =
    (min k (2 ^ m) : ℝ) / (2 : ℝ) ^ m
  rw [hfloor]
  have hjd : j * 2 ^ d ≤ 2 ^ (m + d) := by
    rw [pow_add]
    exact Nat.mul_le_mul_right _ hj
  have hjd' : (j * 2 ^ d : ℝ) ≤ (2 ^ (m + d) : ℝ) := by
    exact_mod_cast hjd
  have hjd'' : ((j * 2 ^ d : ℕ) : ℝ) ≤ (2 ^ (m + d) : ℝ) := by
    exact_mod_cast hjd
  rw [min_eq_left hjd'']
  rw [show (2 ^ (m + d) : ℝ) = (2 : ℝ) ^ m * (2 : ℝ) ^ d by
    norm_num [pow_add]]
  field_simp
  ring_nf
  all_goals
    rw [← hmul, ← hmin]

theorem eventually_dyadicApprox_eq {x : UnitInterval} (hx : x ∈ dyadicUnitSet) :
    ∀ᶠ n in atTop, dyadicApprox n x = x := by
  obtain ⟨m, k, hk⟩ := Set.mem_iUnion.1 hx
  filter_upwards [eventually_ge_atTop m] with n hn
  rw [← hk]
  exact dyadicApprox_eq_gridPoint_of_le (k := (k : ℕ)) hn

end RegularityStructures

end
