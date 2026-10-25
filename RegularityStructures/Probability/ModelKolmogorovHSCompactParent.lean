/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovHSCompactNet

/-!
# Parent cells for intrinsic parabolic nets

The occupied-cell nets used in Hairer--Steele, arXiv:2301.10081v3,
Proposition B.3 must be compatible across scales. Dyadic floor division
shows that a fine cell lies in one coarse cell. Hence each occupied fine
cell has an occupied parent, and the two selected representatives are
within the coarse parabolic mesh radius. No enlargement of the stochastic
index set is involved.
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- The coarse occupied cell of a chosen fine representative. -/
def hsParabolicCellParent (S : Set ParabolicSpace) (n : ℕ)
    (i : HSParabolicOccupiedCell S (n + 1)) : HSParabolicOccupiedCell S n :=
  ⟨hsParabolicCellIndex n (hsParabolicCellRepresentative S (n + 1) i),
    hsParabolicCellRepresentative S (n + 1) i, rfl⟩

end RegularityStructures

end

public section

namespace RegularityStructures

/-- Equality of fine dyadic cells implies equality at every coarser level. -/
theorem hsDyadicCellIndex_eq_of_le {m n : ℕ} (hmn : m ≤ n) (x y : UnitInterval)
    (h : hsDyadicCellIndex n x = hsDyadicCellIndex n y) :
    hsDyadicCellIndex m x = hsDyadicCellIndex m y := by
  have hval (k : ℕ) (z : UnitInterval) :
      (hsDyadicCellIndex k z).val = Nat.floor ((z : ℝ) * (2 : ℝ) ^ k) :=
    min_eq_left (nat_floor_mul_pow_le k z)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have hdiv (z : UnitInterval) :
      Nat.floor ((z : ℝ) * (2 : ℝ) ^ (m + d)) / 2 ^ d =
        Nat.floor ((z : ℝ) * (2 : ℝ) ^ m) := by
    have he := Nat.mul_cast_floor_div_cancel (n := 2 ^ d) (by positivity)
      ((z : ℝ) * (2 : ℝ) ^ m)
    norm_num only [Nat.cast_pow, Nat.cast_ofNat] at he
    simpa only [pow_add, mul_assoc] using he
  have he := congrArg (fun i : Fin (2 ^ (m + d) + 1) => i.val / 2 ^ d) h
  simp only [hval, hdiv] at he
  apply Fin.ext
  simpa only [hval] using he

/-- Fine parabolic cells refine coarse ones inside the unit box. -/
theorem hsParabolicCellIndex_eq_of_le {m n : ℕ} (hmn : m ≤ n)
    {x y : ParabolicSpace}
    (hx : x.1 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ j, x.2 j ∈ Set.Icc (0 : ℝ) 1)
    (hy : y.1 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ j, y.2 j ∈ Set.Icc (0 : ℝ) 1)
    (h : hsParabolicCellIndex n x = hsParabolicCellIndex n y) :
    hsParabolicCellIndex m x = hsParabolicCellIndex m y := by
  apply Prod.ext
  · exact hsDyadicCellIndex_eq_of_le (Nat.mul_le_mul_left 2 hmn)
      ⟨x.1, hx.1⟩ ⟨y.1, hy.1⟩ (congrArg Prod.fst h)
  · funext j
    exact hsDyadicCellIndex_eq_of_le hmn ⟨x.2 j, hx.2 j⟩ ⟨y.2 j, hy.2 j⟩
      (congrFun (congrArg Prod.snd h) j)

/-- A fine cell and its parent have representatives in the same coarse cell. -/
theorem hsParabolicCellParent_radius (S : Set ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ j, x.2 j ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) (i : HSParabolicOccupiedCell S (n + 1)) :
    parabolicNorm ((hsParabolicCellRepresentative S n (hsParabolicCellParent S n i) :
      ParabolicSpace) - hsParabolicCellRepresentative S (n + 1) i) ≤ 4 / (2 : ℝ) ^ n :=
  hsParabolicCellApprox_error_le S hbox n (hsParabolicCellRepresentative S (n + 1) i)

/-- The parent of the fine cell containing a point is its own coarse cell. -/
theorem hsParabolicCellParent_at (S : Set ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ j, x.2 j ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) (x : S) :
    hsParabolicCellParent S n ⟨hsParabolicCellIndex (n + 1) x, x, rfl⟩ =
      ⟨hsParabolicCellIndex n x, x, rfl⟩ := by
  apply Subtype.ext
  exact hsParabolicCellIndex_eq_of_le (Nat.le_succ n)
    (hbox _ (hsParabolicCellApprox S (n + 1) x).property) (hbox _ x.property)
    (hsParabolicCellApprox_index S (n + 1) x)

end RegularityStructures

end
