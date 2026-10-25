/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovHSParabolicGrid

/-!
# Finite nets whose representatives remain inside the compact

Hairer--Steele, arXiv:2301.10081v3, Proposition B.3 assumes moment bounds
only at points of the compact. Replacing the compact by a containing box in
the stochastic hypotheses would strengthen the statement. Instead we retain
one representative of each occupied anisotropic grid cell. This construction
works for any subset of the unit box, including the empty set, and has the
same dimension-five cardinality bound as the ambient grid.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- Clipped dyadic cell index; clipping makes it defined on every real number. -/
def hsDyadicCellIndex (n : ℕ) (x : ℝ) : Fin (2 ^ n + 1) :=
  ⟨min (Nat.floor (x * (2 : ℝ) ^ n)) (2 ^ n), Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- The time-space cell index with the parabolic time refinement. -/
def hsParabolicCellIndex (n : ℕ) (x : ParabolicSpace) : HSParabolicGridIndex n :=
  (hsDyadicCellIndex (2 * n) x.1, fun j => hsDyadicCellIndex n (x.2 j))

/-- Occupied cells carry witnesses in the original set, not in a larger neighbourhood. -/
abbrev HSParabolicOccupiedCell (S : Set ParabolicSpace) (n : ℕ) :=
  {i : HSParabolicGridIndex n // ∃ x : S, hsParabolicCellIndex n x = i}

instance (S : Set ParabolicSpace) (n : ℕ) : Fintype (HSParabolicOccupiedCell S n) :=
  Fintype.ofFinite _

/-- A selected point of the original set in each occupied cell. -/
def hsParabolicCellRepresentative (S : Set ParabolicSpace) (n : ℕ)
    (i : HSParabolicOccupiedCell S n) : S := Classical.choose i.property

/-- Approximation by the representative of the point's own cell. -/
def hsParabolicCellApprox (S : Set ParabolicSpace) (n : ℕ) (x : S) : S :=
  hsParabolicCellRepresentative S n ⟨hsParabolicCellIndex n x, x, rfl⟩

end RegularityStructures

end

public section

namespace RegularityStructures

theorem hsParabolicCellRepresentative_index (S : Set ParabolicSpace) (n : ℕ)
    (i : HSParabolicOccupiedCell S n) :
    hsParabolicCellIndex n (hsParabolicCellRepresentative S n i) = i :=
  Classical.choose_spec i.property

theorem hsParabolicCellApprox_index (S : Set ParabolicSpace) (n : ℕ) (x : S) :
    hsParabolicCellIndex n (hsParabolicCellApprox S n x) = hsParabolicCellIndex n x :=
  hsParabolicCellRepresentative_index S n _

/-- Selecting representatives does not increase the dimension-five covering cost. -/
theorem card_hsParabolicOccupiedCell_le (S : Set ParabolicSpace) (n : ℕ) :
    Fintype.card (HSParabolicOccupiedCell S n) ≤ 16 * 2 ^ (5 * n) := by
  exact (Fintype.card_le_of_injective Subtype.val Subtype.val_injective).trans
    (card_hsParabolicGridIndex_le n)

private theorem hsDyadicCellIndex_val (n : ℕ) (x : UnitInterval) :
    (hsDyadicCellIndex n x).val = Nat.floor ((x : ℝ) * (2 : ℝ) ^ n) := by
  exact min_eq_left (nat_floor_mul_pow_le n x)

/-- A unit-interval point lies between its cell's left endpoint and the next endpoint. -/
theorem hsDyadicCellIndex_bounds (n : ℕ) (x : UnitInterval) :
    (dyadicGridPoint n (hsDyadicCellIndex n x) : ℝ) ≤ x ∧
      (x : ℝ) < (dyadicGridPoint n (hsDyadicCellIndex n x) : ℝ) + 1 / (2 : ℝ) ^ n := by
  have heq : dyadicGridPoint n (hsDyadicCellIndex n x) = dyadicApprox n x := by
    rw [hsDyadicCellIndex_val]
    rfl
  rw [heq]
  exact ⟨dyadicApprox_le n x, lt_dyadicApprox_add n x⟩

/-- The diameter of a single one-dimensional cell is at most one mesh width. -/
theorem hsDyadicCellIndex_abs_sub_le (n : ℕ) (x y : UnitInterval)
    (h : hsDyadicCellIndex n x = hsDyadicCellIndex n y) :
    |(x : ℝ) - y| ≤ 1 / (2 : ℝ) ^ n := by
  have hx := hsDyadicCellIndex_bounds n x
  have hy := hsDyadicCellIndex_bounds n y
  rw [← h] at hy
  rw [abs_sub_le_iff]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- Two points of the same parabolic cell are within four parabolic mesh widths. -/
theorem parabolicNorm_sub_le_of_hsParabolicCellIndex_eq (n : ℕ)
    {x y : ParabolicSpace}
    (hx : x.1 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ j, x.2 j ∈ Set.Icc (0 : ℝ) 1)
    (hy : y.1 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ j, y.2 j ∈ Set.Icc (0 : ℝ) 1)
    (h : hsParabolicCellIndex n x = hsParabolicCellIndex n y) :
    parabolicNorm (x - y) ≤ 4 / (2 : ℝ) ^ n := by
  have ht := hsDyadicCellIndex_abs_sub_le (2 * n) ⟨x.1, hx.1⟩ ⟨y.1, hy.1⟩
    (congrArg Prod.fst h)
  have hs (j : Fin 3) := hsDyadicCellIndex_abs_sub_le n ⟨x.2 j, hx.2 j⟩ ⟨y.2 j, hy.2 j⟩
    (congrFun (congrArg Prod.snd h) j)
  have ht' : Real.sqrt |x.1 - y.1| ≤ 1 / (2 : ℝ) ^ n := by
    apply Real.sqrt_le_iff.2
    refine ⟨by positivity, ht.trans_eq ?_⟩
    rw [show 2 * n = n * 2 by omega, pow_mul]
    ring
  have hsum : (∑ j : Fin 3, |x.2 j - y.2 j|) ≤ 3 / (2 : ℝ) ^ n := by
    calc
      _ ≤ ∑ _j : Fin 3, 1 / (2 : ℝ) ^ n := Finset.sum_le_sum fun j _ => hs j
      _ = _ := by simp; ring
  change Real.sqrt _ + _ ≤ _
  exact (add_le_add ht' hsum).trans_eq (by ring)

/-- The occupied-cell approximations converge at the parabolic mesh rate and stay in `S`. -/
theorem hsParabolicCellApprox_error_le (S : Set ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ j, x.2 j ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) (x : S) :
    parabolicNorm ((hsParabolicCellApprox S n x : ParabolicSpace) - x) ≤
      4 / (2 : ℝ) ^ n :=
  parabolicNorm_sub_le_of_hsParabolicCellIndex_eq n
    (hbox _ (hsParabolicCellApprox S n x).property) (hbox _ x.property)
    (hsParabolicCellApprox_index S n x)

end RegularityStructures

end
