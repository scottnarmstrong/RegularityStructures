/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovGammaAll
import Mathlib.Data.Fintype.Card
public import RegularityStructures.Probability.ModelKolmogorovGlobalGammaChen
public import RegularityStructures.Probability.ModelKolmogorovGlobalGammaRightIncrement

/-!
# The `DΓ` / non-`DΓ` split in the Gamma Chen source

For a strictly lower Gamma coordinate, the Chen source is a finite sum of products. The products
whose two factors are in the deterministic sector `DΓ` are separated from the remaining products.
The former are controlled pathwise and the latter retain the moment reserve. This is the
source-level split used in the finite-sector induction of the Kolmogorov criterion for models.

The identities are the coordinate form of Hairer [Hai14, (2.17)] and the mixed endpoint formula used
in [Hai14, Theorem 10.7].
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {𝒯 : RegularityStructure ι}

/-- The indices strictly intermediate between `j` and `i`. -/
def gammaIntermediate (𝒯 : RegularityStructure ι) (i j : ι) : Finset ι :=
  by
    classical
    exact Finset.univ.filter
      (fun k => 𝒯.deg j < 𝒯.deg k ∧ 𝒯.deg k < 𝒯.deg i)

/-- The intermediate indices with at least one non-deterministic factor. -/
def gammaGoodIntermediate (𝒯 : RegularityStructure ι)
    (D : Set (ι × ι)) (i j : ι) : Finset ι :=
  by
    classical
    exact (gammaIntermediate 𝒯 i j).filter
      (fun k => ¬((i, k) ∈ D ∧ (k, j) ∈ D))

/-- The intermediate indices with two deterministic factors. -/
def gammaBadIntermediate (𝒯 : RegularityStructure ι)
    (D : Set (ι × ι)) (i j : ι) : Finset ι :=
  by
    classical
    exact (gammaIntermediate 𝒯 i j).filter
      (fun k => (i, k) ∈ D ∧ (k, j) ∈ D)

private theorem gammaIntermediate_split
    (𝒯 : RegularityStructure ι) (D : Set (ι × ι)) (i j : ι) (f : ι → ℝ) :
    ∑ k ∈ gammaIntermediate 𝒯 i j, f k =
    ∑ k ∈ gammaGoodIntermediate 𝒯 D i j, f k +
        ∑ k ∈ gammaBadIntermediate 𝒯 D i j, f k := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not
    (gammaIntermediate 𝒯 i j)
    (fun k => ¬((i, k) ∈ D ∧ (k, j) ∈ D))]
  simp only [gammaGoodIntermediate, gammaBadIntermediate]
  simp only [not_not]

/-- The good part of a left-endpoint Chen source. -/
def gammaSplitLeftGoodTerm
    (M : Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (i j : ι) (x y z : ParabolicSpace) : ℝ :=
  M.gammaMap z y (Pi.single i 1) j +
    ∑ k ∈ gammaGoodIntermediate 𝒯 D i j,
      M.gammaMap y x (Pi.single i 1) k *
        M.gammaMap z y (Pi.single k 1) j

/-- The pathwise deterministic part of a left-endpoint Chen source. -/
def gammaSplitLeftBadTerm
    (M : Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (i j : ι) (x y z : ParabolicSpace) : ℝ :=
  ∑ k ∈ gammaBadIntermediate 𝒯 D i j,
    M.gammaMap y x (Pi.single i 1) k *
      M.gammaMap z y (Pi.single k 1) j

/-- The good part of a right-endpoint Chen source. -/
def gammaSplitRightGoodTerm
    (M : Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (i j : ι) (x y z : ParabolicSpace) : ℝ :=
  M.gammaMap y z (Pi.single i 1) j +
    ∑ k ∈ gammaGoodIntermediate 𝒯 D i j,
      M.gammaMap y z (Pi.single i 1) k *
        M.gammaMap x y (Pi.single k 1) j

/-- The pathwise deterministic part of a right-endpoint Chen source. -/
def gammaSplitRightBadTerm
    (M : Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (i j : ι) (x y z : ParabolicSpace) : ℝ :=
  ∑ k ∈ gammaBadIntermediate 𝒯 D i j,
    M.gammaMap y z (Pi.single i 1) k *
      M.gammaMap x y (Pi.single k 1) j

theorem gammaSplitLeftTerm_eq
    (M : Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (i j : ι) (x y z : ParabolicSpace)
    (hji : 𝒯.deg j < 𝒯.deg i) :
    M.gammaMap z x (Pi.single i 1) j - M.gammaMap y x (Pi.single i 1) j =
      gammaSplitLeftGoodTerm M D i j x y z +
        gammaSplitLeftBadTerm M D i j x y z := by
  rw [Model.gammaMap_single_left_increment_lower M x y z hji]
  change M.gammaMap z y (Pi.single i 1) j +
      (∑ k ∈ gammaIntermediate 𝒯 i j,
        M.gammaMap y x (Pi.single i 1) k *
          M.gammaMap z y (Pi.single k 1) j) =
    (M.gammaMap z y (Pi.single i 1) j +
      ∑ k ∈ gammaGoodIntermediate 𝒯 D i j,
        M.gammaMap y x (Pi.single i 1) k *
          M.gammaMap z y (Pi.single k 1) j) +
      ∑ k ∈ gammaBadIntermediate 𝒯 D i j,
        M.gammaMap y x (Pi.single i 1) k *
          M.gammaMap z y (Pi.single k 1) j
  have hs := gammaIntermediate_split 𝒯 D i j
    (fun k => M.gammaMap y x (Pi.single i 1) k *
      M.gammaMap z y (Pi.single k 1) j)
  rw [hs]
  ring

theorem gammaSplitRightTerm_eq
    (M : Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (i j : ι) (x y z : ParabolicSpace)
    (hji : 𝒯.deg j < 𝒯.deg i) :
    M.gammaMap x z (Pi.single i 1) j - M.gammaMap x y (Pi.single i 1) j =
      gammaSplitRightGoodTerm M D i j x y z +
        gammaSplitRightBadTerm M D i j x y z := by
  rw [Model.gammaMap_single_right_increment_lower M x y z hji]
  change M.gammaMap y z (Pi.single i 1) j +
      (∑ k ∈ gammaIntermediate 𝒯 i j,
        M.gammaMap y z (Pi.single i 1) k *
          M.gammaMap x y (Pi.single k 1) j) =
    (M.gammaMap y z (Pi.single i 1) j +
      ∑ k ∈ gammaGoodIntermediate 𝒯 D i j,
        M.gammaMap y z (Pi.single i 1) k *
          M.gammaMap x y (Pi.single k 1) j) +
      ∑ k ∈ gammaBadIntermediate 𝒯 D i j,
        M.gammaMap y z (Pi.single i 1) k *
          M.gammaMap x y (Pi.single k 1) j
  have hs := gammaIntermediate_split 𝒯 D i j
    (fun k => M.gammaMap y z (Pi.single i 1) k *
      M.gammaMap x y (Pi.single k 1) j)
  rw [hs]
  ring

theorem gammaSplitLeftTerm_enorm_le
    (M : Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (i j : ι) (x y z : ParabolicSpace)
    (hji : 𝒯.deg j < 𝒯.deg i) :
    ‖M.gammaMap z x (Pi.single i 1) j - M.gammaMap y x (Pi.single i 1) j‖ₑ ≤
      ‖gammaSplitLeftGoodTerm M D i j x y z‖ₑ +
        ‖gammaSplitLeftBadTerm M D i j x y z‖ₑ := by
  rw [gammaSplitLeftTerm_eq M D i j x y z hji]
  exact enorm_add_le _ _

theorem gammaSplitRightTerm_enorm_le
    (M : Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (i j : ι) (x y z : ParabolicSpace)
    (hji : 𝒯.deg j < 𝒯.deg i) :
    ‖M.gammaMap x z (Pi.single i 1) j - M.gammaMap x y (Pi.single i 1) j‖ₑ ≤
      ‖gammaSplitRightGoodTerm M D i j x y z‖ₑ +
        ‖gammaSplitRightBadTerm M D i j x y z‖ₑ := by
  rw [gammaSplitRightTerm_eq M D i j x y z hji]
  exact enorm_add_le _ _

end RegularityStructures

end
