/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovGammaDiffSource
public import RegularityStructures.Probability.ModelKolmogorovGammaSplit
public import RegularityStructures.Probability.ModelKolmogorovGlobalGammaChen
public import RegularityStructures.Probability.ModelKolmogorovGlobalGammaRightMoments

/-!
# Algebra for the split two-model Gamma source

The two-model cocycle increment is split into the mixed channels and the two-deterministic-factor
channels. This is the algebraic bridge used by the annular Gamma induction in the Kolmogorov
criterion for models; cf. Hairer [Hai14, (2.17)] and Hairer--Steele [HS23, Proposition B.3].
-/

@[expose] public noncomputable section

open Set

namespace RegularityStructures

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace Ω] {𝒯 : RegularityStructure ι}

omit [MeasurableSpace Ω] in
theorem gammaDiffSplitLeftTerm_eq
    (M₁ M₂ : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (i j : ι) (x y z : ParabolicSpace) (ω : Ω)
    (hij : 𝒯.deg j < 𝒯.deg i) :
    ((M₁ ω).gammaMap z x (Pi.single i 1) j -
        (M₂ ω).gammaMap z x (Pi.single i 1) j) -
      ((M₁ ω).gammaMap y x (Pi.single i 1) j -
        (M₂ ω).gammaMap y x (Pi.single i 1) j) =
      gammaDiffSplitLeftGoodTerm M₁ M₂ D i j x y z ω +
        gammaSplitLeftBadTermDiff (M₁ ω) (M₂ ω) D i j x y z := by
  classical
  rw [Model.gammaMap_single_diff_left_increment_lower (M₁ ω) (M₂ ω) x y z hij]
  unfold gammaDiffSplitLeftGoodTerm gammaSplitLeftBadTermDiff
  let s := Finset.univ.filter
    (fun k => 𝒯.deg j < 𝒯.deg k ∧ 𝒯.deg k < 𝒯.deg i)
  let f : ι → ℝ := fun k =>
    ((M₁ ω).gammaMap y x (Pi.single i 1) k -
        (M₂ ω).gammaMap y x (Pi.single i 1) k) *
        (M₁ ω).gammaMap z y (Pi.single k 1) j +
      (M₂ ω).gammaMap y x (Pi.single i 1) k *
        ((M₁ ω).gammaMap z y (Pi.single k 1) j -
          (M₂ ω).gammaMap z y (Pi.single k 1) j)
  have hsplit : ∑ k ∈ s, f k =
      ∑ k ∈ gammaGoodIntermediate 𝒯 D i j, f k +
        ∑ k ∈ gammaBadIntermediate 𝒯 D i j, f k := by
    rw [← Finset.sum_filter_add_sum_filter_not s
      (fun k => ¬((i, k) ∈ D ∧ (k, j) ∈ D))]
    simp [s, f, gammaIntermediate, gammaGoodIntermediate,
      gammaBadIntermediate]
  rw [hsplit]
  dsimp [f]
  ring

omit [MeasurableSpace Ω] in
theorem gammaDiffSplitRightTerm_eq
    (M₁ M₂ : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (i j : ι) (x y z : ParabolicSpace) (ω : Ω)
    (hij : 𝒯.deg j < 𝒯.deg i) :
    ((M₁ ω).gammaMap x z (Pi.single i 1) j -
        (M₂ ω).gammaMap x z (Pi.single i 1) j) -
      ((M₁ ω).gammaMap x y (Pi.single i 1) j -
        (M₂ ω).gammaMap x y (Pi.single i 1) j) =
      gammaDiffSplitRightGoodTerm M₁ M₂ D i j x y z ω +
        gammaSplitRightBadTermDiff (M₁ ω) (M₂ ω) D i j x y z := by
  classical
  rw [gammaMap_single_diff_right_increment_lower
    (M₁ ω) (M₂ ω) x y z hij]
  unfold gammaDiffSplitRightGoodTerm gammaSplitRightBadTermDiff
  let s := Finset.univ.filter
    (fun k => 𝒯.deg j < 𝒯.deg k ∧ 𝒯.deg k < 𝒯.deg i)
  let f : ι → ℝ := fun k =>
    ((M₁ ω).gammaMap y z (Pi.single i 1) k -
        (M₂ ω).gammaMap y z (Pi.single i 1) k) *
        (M₁ ω).gammaMap x y (Pi.single k 1) j +
      (M₂ ω).gammaMap y z (Pi.single i 1) k *
        ((M₁ ω).gammaMap x y (Pi.single k 1) j -
          (M₂ ω).gammaMap x y (Pi.single k 1) j)
  have hsplit : ∑ k ∈ s, f k =
      ∑ k ∈ gammaGoodIntermediate 𝒯 D i j, f k +
        ∑ k ∈ gammaBadIntermediate 𝒯 D i j, f k := by
    rw [← Finset.sum_filter_add_sum_filter_not s
      (fun k => ¬((i, k) ∈ D ∧ (k, j) ∈ D))]
    simp [s, f, gammaIntermediate, gammaGoodIntermediate,
      gammaBadIntermediate]
  rw [hsplit]
  dsimp [f]
  ring

end RegularityStructures

end
