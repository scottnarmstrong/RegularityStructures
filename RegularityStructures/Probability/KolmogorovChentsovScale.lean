/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.KolmogorovChentsovDyadic
public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.Topology.MetricSpace.Basic

/-!
# Dyadic scale selection on the unit interval

The radius `4 * 2⁻ⁿ` is the scale appearing in the finite close-pair
estimates.  This file proves that it is comparable to every nonzero distance
on the unit interval, with constants independent of the points.
-/

@[expose] public section

open scoped ENNReal NNReal Topology

namespace RegularityStructures

noncomputable def dyadicBase (n : ℕ) : ℝ≥0∞ :=
  ((2 : ℝ≥0∞)⁻¹) ^ n

theorem dyadicBase_pos (n : ℕ) : 0 < dyadicBase n := by
  dsimp [dyadicBase]
  exact ENNReal.pow_pos (ENNReal.inv_pos.2 (by norm_num)) n

theorem dyadicBase_ne_top (n : ℕ) : dyadicBase n ≠ ∞ := by
  simp [dyadicBase]

theorem ofReal_inv_two_pow (n : ℕ) :
    ENNReal.ofReal (1 / (2 : ℝ) ^ n) = dyadicBase n := by
  rw [div_eq_mul_inv, ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by positivity)]
  rw [ENNReal.inv_pow]
  norm_num [dyadicBase]

theorem edist_unitInterval_le_one (x y : UnitInterval) :
    edist x y ≤ 1 := by
  rw [edist_dist, Subtype.dist_eq, Real.dist_eq]
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  rw [abs_le]
  constructor <;> nlinarith [x.2.1, x.2.2, y.2.1, y.2.2]

theorem dyadicBase_succ (n : ℕ) :
    dyadicBase (n + 1) * 2 = dyadicBase n := by
  unfold dyadicBase
  rw [pow_succ]
  calc
    ((2 : ℝ≥0∞)⁻¹ ^ n * (2 : ℝ≥0∞)⁻¹) * 2 =
        (2 : ℝ≥0∞)⁻¹ ^ n * ((2 : ℝ≥0∞)⁻¹ * 2) := by ac_rfl
    _ = (2 : ℝ≥0∞)⁻¹ ^ n := by
      rw [ENNReal.inv_mul_cancel] <;> norm_num

theorem dyadicBase_selection (x y : UnitInterval) (hxy : edist x y ≠ 0) :
    ∃ n : ℕ, edist x y ≤ dyadicBase n ∧
      dyadicBase n ≤ 2 * edist x y := by
  let d : ℝ≥0∞ := edist x y
  have hd : d ≤ 1 := edist_unitInterval_le_one x y
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_two_pow_lt hxy
  have hex : ∃ k : ℕ, dyadicBase k < d := by
    exact ⟨n, by simpa [dyadicBase] using hn⟩
  let k := Nat.find hex
  have hk : dyadicBase k < d := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro hkzero
    have hkzero' : Nat.find hex = 0 := by simpa [k] using hkzero
    change dyadicBase (Nat.find hex) < d at hk
    rw [hkzero'] at hk
    have hone : (1 : ℝ≥0∞) < d := by simpa [dyadicBase] using hk
    exact (by norm_num : ¬((1 : ℝ≥0∞) < 1)) (hone.trans_le hd)
  obtain ⟨m, hk_eq⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hprev : d ≤ dyadicBase m := by
    by_contra h
    have hlt : dyadicBase m < d := lt_of_not_ge h
    have hkm : k ≤ m := Nat.find_min' hex hlt
    rw [hk_eq] at hkm
    omega
  refine ⟨m, hprev, ?_⟩
  have hnext : dyadicBase (m + 1) < d := by simpa [hk_eq] using hk
  have hmul : dyadicBase (m + 1) * 2 ≤ d * 2 := by
    gcongr
  rw [dyadicBase_succ] at hmul
  simpa [mul_comm] using hmul

end RegularityStructures

end
