/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.KolmogorovChentsovTail
public import RegularityStructures.Probability.KolmogorovChentsovGrid

/-!
# Hölder control on the dense dyadic skeleton

Successive dyadic approximants are telescoped in the complete target.  The
geometric tail estimate then gives a Hölder bound on the dyadic points, from
which the completion module constructs the full modification.
-/

@[expose] public section

open Filter Set
open scoped ENNReal NNReal Topology

namespace RegularityStructures

noncomputable def dyadicTailCoeff (r : ℝ≥0) : ℝ≥0∞ :=
  ((2 : ℝ≥0∞)⁻¹) ^ (r : ℝ) *
    (1 - ((2 : ℝ≥0∞)⁻¹) ^ (r : ℝ))⁻¹

theorem dyadicTailCoeff_lt_top {r : ℝ≥0} (hr : 0 < r) :
    dyadicTailCoeff r < ∞ := by
  unfold dyadicTailCoeff
  apply ENNReal.mul_lt_top
  · exact ENNReal.rpow_lt_top_of_nonneg (by positivity) (by simp)
  · apply ENNReal.inv_lt_top.2
    exact tsub_pos_iff_lt.2 (ENNReal.rpow_lt_one (by norm_num) hr)

theorem dyadicApprox_eventually_shifted {x : UnitInterval}
    (hx : x ∈ dyadicUnitSet) (n : ℕ) :
    ∀ᶠ k in atTop, dyadicApprox (n + k) x = x := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_dyadicApprox_eq hx)
  filter_upwards [eventually_ge_atTop N] with k hk
  exact hN (n + k) (by omega)

theorem dyadicApprox_step_grid_bound {E : Type*} [PseudoEMetricSpace E]
    {f : UnitInterval → E} {L : ℝ≥0∞} {r : ℝ≥0}
    (hgrid : ∀ n : ℕ, ∀ u v : UnitInterval,
      u ∈ dyadicGridFinset n → v ∈ dyadicGridFinset n →
      edist u v ≤ ENNReal.ofReal (4 / (2 : ℝ) ^ n) →
      edist (f u) (f v) ≤ L * (dyadicBase n) ^ (r : ℝ))
    {x : UnitInterval} (n k : ℕ) :
    edist (f (dyadicApprox (n + k) x))
        (f (dyadicApprox (n + k + 1) x)) ≤
      L * (dyadicBase (n + k + 1)) ^ (r : ℝ) := by
  apply hgrid (n + k + 1) (dyadicApprox (n + k) x)
    (dyadicApprox (n + k + 1) x)
  · exact dyadicApprox_mem_finer_gridFinset (n + k) x
  · exact dyadicApprox_mem_gridFinset (n + k + 1) x
  · exact edist_dyadicApprox_succ_le (n + k) x

theorem dyadic_telescope_bound {E : Type*} [PseudoEMetricSpace E]
    {f : UnitInterval → E} {L : ℝ≥0∞} {r : ℝ≥0}
    (hr : 0 < r)
    (hgrid : ∀ n : ℕ, ∀ u v : UnitInterval,
      u ∈ dyadicGridFinset n → v ∈ dyadicGridFinset n →
      edist u v ≤ ENNReal.ofReal (4 / (2 : ℝ) ^ n) →
      edist (f u) (f v) ≤ L * (dyadicBase n) ^ (r : ℝ))
    {x : UnitInterval} (hx : x ∈ dyadicUnitSet) (n : ℕ) :
    edist (f (dyadicApprox n x)) (f x) ≤
      L * (dyadicBase n) ^ (r : ℝ) * dyadicTailCoeff r := by
  have hstep : ∀ k : ℕ,
      edist (f (dyadicApprox (n + k) x))
          (f (dyadicApprox (n + k + 1) x)) ≤
        L * (dyadicBase (n + k + 1)) ^ (r : ℝ) := by
    intro k
    exact dyadicApprox_step_grid_bound (f := f) (L := L) (r := r) hgrid n k
  have heq : ∀ᶠ k in atTop,
      f (dyadicApprox (n + k) x) = f x := by
    filter_upwards [dyadicApprox_eventually_shifted hx n] with k hk
    simp [hk]
  have htel : edist (f (dyadicApprox n x)) (f x) ≤
      ∑' k : ℕ, L * (dyadicBase (n + k + 1)) ^ (r : ℝ) := by
    simpa only [Nat.add_zero] using
      (edist_le_tsum_of_eventually_eq
        (u := fun k => f (dyadicApprox (n + k) x))
        (x := f x) (n := 0)
        (c := fun k => L * (dyadicBase (n + k + 1)) ^ (r : ℝ))
        (by
          intro k
          simpa [Nat.add_assoc] using hstep k)
        heq)
  calc
    edist (f (dyadicApprox n x)) (f x) ≤
        ∑' k : ℕ, L * (dyadicBase (n + k + 1)) ^ (r : ℝ) := htel
    _ = L * ∑' k : ℕ, (dyadicBase (n + k + 1)) ^ (r : ℝ) :=
      ENNReal.tsum_mul_left
    _ = L * ((dyadicBase n) ^ (r : ℝ) * dyadicTailCoeff r) := by
      rw [dyadicBase_tail_rpow_sum hr n]
      simp [dyadicTailCoeff]
    _ = L * (dyadicBase n) ^ (r : ℝ) * dyadicTailCoeff r := by ring

theorem holderOnWith_dyadic {E : Type*} [PseudoEMetricSpace E]
    {f : UnitInterval → E} {L : ℝ≥0∞} {r : ℝ≥0}
    (hr : 0 < r) (hL : L ≠ ∞)
    (hgrid : ∀ n : ℕ, ∀ u v : UnitInterval,
      u ∈ dyadicGridFinset n → v ∈ dyadicGridFinset n →
      edist u v ≤ ENNReal.ofReal (4 / (2 : ℝ) ^ n) →
      edist (f u) (f v) ≤ L * (dyadicBase n) ^ (r : ℝ)) :
    HolderOnWith
      (L * (1 + 2 * dyadicTailCoeff r) * (2 : ℝ≥0∞) ^ (r : ℝ)).toNNReal
      r f dyadicUnitSet := by
  let K : ℝ≥0∞ := L * (1 + 2 * dyadicTailCoeff r) *
    (2 : ℝ≥0∞) ^ (r : ℝ)
  have hK : K ≠ ∞ := by
    dsimp [K]
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · exact hL
      · have htwo : (2 : ℝ≥0∞) * dyadicTailCoeff r ≠ ∞ :=
          ENNReal.mul_ne_top (by simp) (dyadicTailCoeff_lt_top hr).ne
        exact (ENNReal.add_ne_top).2 ⟨by simp, htwo⟩
    · have hpow : (2 : ℝ≥0∞) ^ (r : ℝ) < ∞ :=
        ENNReal.rpow_lt_top_of_nonneg (by positivity) (by simp)
      exact hpow.ne
  let C : ℝ≥0 := K.toNNReal
  change HolderOnWith C r f dyadicUnitSet
  intro x hx y hy
  by_cases hxy : edist x y = 0
  · have hxy' : x = y := edist_eq_zero.mp hxy
    subst y
    simp
  obtain ⟨n, hdn, hn2⟩ := dyadicBase_selection x y hxy
  have hax : edist (dyadicApprox n x) x ≤ dyadicBase n := by
    rw [← ofReal_inv_two_pow n]
    simpa [edist_dist, Subtype.dist_eq, Real.dist_eq, dist_comm] using
      edist_dyadicApprox_le n x
  have hby : edist (dyadicApprox n y) y ≤ dyadicBase n := by
    rw [← ofReal_inv_two_pow n]
    simpa [edist_dist, Subtype.dist_eq, Real.dist_eq, dist_comm] using
      edist_dyadicApprox_le n y
  have hab : edist (dyadicApprox n x) (dyadicApprox n y) ≤
      ENNReal.ofReal (4 / (2 : ℝ) ^ n) := by
    rw [ofReal_four_div_two_pow n]
    calc
      edist (dyadicApprox n x) (dyadicApprox n y) ≤
          edist (dyadicApprox n x) x + edist x (dyadicApprox n y) :=
        edist_triangle _ _ _
      _ ≤ edist (dyadicApprox n x) x +
          (edist x y + edist y (dyadicApprox n y)) :=
        add_le_add le_rfl (edist_triangle x y (dyadicApprox n y))
      _ ≤ dyadicBase n + edist x y + dyadicBase n := by
        calc
          edist (dyadicApprox n x) x +
              (edist x y + edist y (dyadicApprox n y)) ≤
              dyadicBase n + (edist x y + edist y (dyadicApprox n y)) :=
            add_le_add hax (le_refl _)
          _ ≤ dyadicBase n + (edist x y + dyadicBase n) := by
            exact add_le_add (le_refl _) (add_le_add (le_refl _)
              (by simpa [edist_comm] using hby))
          _ = dyadicBase n + edist x y + dyadicBase n := by ring
      _ ≤ dyadicBase n + dyadicBase n + dyadicBase n := by
        gcongr
      _ ≤ 4 * dyadicBase n := by
        calc
          dyadicBase n + dyadicBase n + dyadicBase n =
              3 * dyadicBase n := by ring
          _ ≤ 4 * dyadicBase n := by
            gcongr
            norm_num
  have hmid : edist (f (dyadicApprox n x)) (f (dyadicApprox n y)) ≤
      L * (dyadicBase n) ^ (r : ℝ) :=
    hgrid n _ _ (dyadicApprox_mem_gridFinset n x)
      (dyadicApprox_mem_gridFinset n y) hab
  have htailx := dyadic_telescope_bound hr hgrid hx n
  have htaily := dyadic_telescope_bound hr hgrid hy n
  have hsum : edist (f x) (f y) ≤
      L * (dyadicBase n) ^ (r : ℝ) * (1 + 2 * dyadicTailCoeff r) := by
    calc
      edist (f x) (f y) ≤
          edist (f x) (f (dyadicApprox n x)) +
            edist (f (dyadicApprox n x)) (f (dyadicApprox n y)) +
              edist (f (dyadicApprox n y)) (f y) := by
        calc
          edist (f x) (f y) ≤
              edist (f x) (f (dyadicApprox n x)) +
                edist (f (dyadicApprox n x)) (f y) := edist_triangle _ _ _
          _ ≤ edist (f x) (f (dyadicApprox n x)) +
              (edist (f (dyadicApprox n x)) (f (dyadicApprox n y)) +
                edist (f (dyadicApprox n y)) (f y)) :=
            add_le_add le_rfl
              (edist_triangle (f (dyadicApprox n x))
                (f (dyadicApprox n y)) (f y))
          _ = _ := by ac_rfl
      _ ≤ L * (dyadicBase n) ^ (r : ℝ) * dyadicTailCoeff r +
          (L * (dyadicBase n) ^ (r : ℝ) +
            (L * (dyadicBase n) ^ (r : ℝ) * dyadicTailCoeff r)) := by
        have htailx' : edist (f x) (f (dyadicApprox n x)) ≤
            L * (dyadicBase n) ^ (r : ℝ) * dyadicTailCoeff r := by
          simpa [edist_comm] using htailx
        simpa [add_assoc] using
          (add_le_add (add_le_add htailx' hmid) htaily)
      _ = L * (dyadicBase n) ^ (r : ℝ) *
          (1 + 2 * dyadicTailCoeff r) := by ring
  have hbasepow : (dyadicBase n) ^ (r : ℝ) ≤
      (2 * edist x y) ^ (r : ℝ) := by
    exact ENNReal.rpow_le_rpow hn2 (by positivity)
  calc
    edist (f x) (f y) ≤
        L * (dyadicBase n) ^ (r : ℝ) * (1 + 2 * dyadicTailCoeff r) := hsum
    _ ≤ L * (2 * edist x y) ^ (r : ℝ) *
          (1 + 2 * dyadicTailCoeff r) := by gcongr
    _ = K * edist x y ^ (r : ℝ) := by
      dsimp [K]
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
      ring
    _ = (C : ℝ≥0∞) * edist x y ^ (r : ℝ) := by
      rw [show (C : ℝ≥0∞) = K by
        dsimp [C]
        exact ENNReal.coe_toNNReal hK]

end RegularityStructures

end
