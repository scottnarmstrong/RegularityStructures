/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovPiHalfCellNet
public import RegularityStructures.Probability.ModelKolmogorovPiHalfAssemblyBox
public import RegularityStructures.Probability.ModelKolmogorovPiHalfAssemblyDyadic

/-!
# Occupied cells at level `j`

At dyadic level `j` (scale `s_j = 2^{-(j+2)}`) the occupied cells of the mesh `2^{-N}`,
`N = ⌊j/4⌋ + 4`, of a subset `T` of the unit box have representatives in `T` at parabolic distance
at most `s_j^{1/4}` from every point of their cell, and there are at most
`2^{24} · 2^{5⌊j/4⌋}` of them.  `piHalfCellRep T j c` lists them by `c < piHalfCellCount T j`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

/-- The cell level `⌊j/4⌋ + 4`. -/
def piHalfCellLevel (j : ℕ) : ℕ := j / 4 + 4

/-- The number of occupied cells of `T` at level `j`. -/
noncomputable def piHalfCellCount (T : Set ParabolicSpace) (j : ℕ) : ℕ :=
  Fintype.card (HSParabolicOccupiedCell T (piHalfCellLevel j))

/-- The `c`-th occupied cell representative (junk `0` for `c` out of range). -/
noncomputable def piHalfCellRep (T : Set ParabolicSpace) (j c : ℕ) : ParabolicSpace :=
  if h : c < piHalfCellCount T j then
    ((hsParabolicCellRepresentative T (piHalfCellLevel j)
      ((Fintype.equivFin (HSParabolicOccupiedCell T (piHalfCellLevel j))).symm ⟨c, h⟩) : T) :
        ParabolicSpace)
  else 0

/-- The index of the occupied cell of `x ∈ T`. -/
noncomputable def piHalfCellOf (T : Set ParabolicSpace) (j : ℕ) (x : T) : ℕ :=
  (Fintype.equivFin (HSParabolicOccupiedCell T (piHalfCellLevel j))
    ⟨hsParabolicCellIndex (piHalfCellLevel j) x, x, rfl⟩ : ℕ)

theorem piHalfCellCount_le (T : Set ParabolicSpace) (j : ℕ) :
    (piHalfCellCount T j : ℝ) ≤ (2 : ℝ) ^ 24 * (2 : ℝ) ^ (5 * (j / 4)) := by
  have h := card_hsParabolicOccupiedCell_le T (piHalfCellLevel j)
  have h2 : piHalfCellCount T j ≤ 2 ^ 24 * 2 ^ (5 * (j / 4)) := by
    refine h.trans (le_of_eq ?_)
    unfold piHalfCellLevel
    rw [show 5 * (j / 4 + 4) = 5 * (j / 4) + 20 by ring, pow_add]
    ring
  exact_mod_cast h2

theorem piHalfCellOf_lt (T : Set ParabolicSpace) (j : ℕ) (x : T) :
    piHalfCellOf T j x < piHalfCellCount T j :=
  Fin.is_lt _

theorem piHalfCellRep_cellOf (T : Set ParabolicSpace) (j : ℕ) (x : T) :
    piHalfCellRep T j (piHalfCellOf T j x) =
      (hsParabolicCellApprox T (piHalfCellLevel j) x : ParabolicSpace) := by
  unfold piHalfCellRep piHalfCellOf hsParabolicCellApprox piHalfCellCount
  simp only [Fin.is_lt, ↓reduceDIte, Fin.eta, Equiv.symm_apply_apply]

theorem piHalfCellRep_cellOf_mem (T : Set ParabolicSpace) (j : ℕ) (x : T) :
    piHalfCellRep T j (piHalfCellOf T j x) ∈ T := by
  rw [piHalfCellRep_cellOf]
  exact (hsParabolicCellApprox T (piHalfCellLevel j) x).2

/-- Points are within `s_j^{1/4}` of their cell representative. -/
theorem parabolicNorm_sub_piHalfCellRep_le {T : Set ParabolicSpace} (hT : T ⊆ piHalfUnitBox)
    (j : ℕ) (x : T) :
    parabolicNorm ((x : ParabolicSpace) - piHalfCellRep T j (piHalfCellOf T j x)) ≤
      piHalfScale j ^ (1 / 4 : ℝ) := by
  rw [piHalfCellRep_cellOf]
  refine (parabolicNorm_sub_cellRepresentative_le T (fun y hy => hT hy)
    (piHalfCellLevel j) x.2).trans ?_
  have h1 : (4 : ℝ) * (2 : ℝ) ^ (-((piHalfCellLevel j : ℕ) : ℤ)) =
      (1 / 2 : ℝ) ^ (j / 4 + 2) := by
    unfold piHalfCellLevel
    rw [zpow_neg, zpow_natCast, one_div, inv_pow, show j / 4 + 4 = (j / 4 + 2) + 2 by ring,
      pow_add]
    field_simp
    norm_num
  rw [h1]
  have h2 : piHalfScale j ^ (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ (((j : ℝ) + 2) / 4) := by
    unfold piHalfScale
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    push_cast
    ring
  rw [h2, show (1 / 2 : ℝ) ^ (j / 4 + 2) = (1 / 2 : ℝ) ^ (((j / 4 + 2 : ℕ) : ℝ)) from
    (Real.rpow_natCast _ _).symm]
  refine Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) ?_
  have : j + 2 ≤ 4 * (j / 4 + 2) := by omega
  have h3 : ((j : ℝ) + 2) ≤ 4 * ((j / 4 + 2 : ℕ) : ℝ) := by exact_mod_cast this
  linarith

end RegularityStructures

end
