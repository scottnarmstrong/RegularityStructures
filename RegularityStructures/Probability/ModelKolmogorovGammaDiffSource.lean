/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovGammaDiffSplit
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Good-channel source moments for two-model Gamma differences

The two-model Chen source is split before applying Holder.  This file keeps
the channels having at least one non-`DΓ` factor.  Such a channel retains the
`κbar` reserve supplied by the non-deterministic factor; the complementary
two-`DΓ` channel is handled pathwise.
-/

@[expose] public noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal NNReal

namespace RegularityStructures

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝒯 : RegularityStructure ι}

def gammaDiffSplitLeftGoodTerm
    (M₁ M₂ : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (i j : ι) (x y z : ParabolicSpace) (ω : Ω) : ℝ :=
  (M₁ ω).gammaMap z y (Pi.single i 1) j -
      (M₂ ω).gammaMap z y (Pi.single i 1) j +
    ∑ k ∈ gammaGoodIntermediate 𝒯 D i j,
      (((M₁ ω).gammaMap y x (Pi.single i 1) k -
          (M₂ ω).gammaMap y x (Pi.single i 1) k) *
          (M₁ ω).gammaMap z y (Pi.single k 1) j +
        (M₂ ω).gammaMap y x (Pi.single i 1) k *
          ((M₁ ω).gammaMap z y (Pi.single k 1) j -
            (M₂ ω).gammaMap z y (Pi.single k 1) j))

def gammaDiffSplitRightGoodTerm
    (M₁ M₂ : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (i j : ι) (x y z : ParabolicSpace) (ω : Ω) : ℝ :=
  (M₁ ω).gammaMap y z (Pi.single i 1) j -
      (M₂ ω).gammaMap y z (Pi.single i 1) j +
    ∑ k ∈ gammaGoodIntermediate 𝒯 D i j,
      (((M₁ ω).gammaMap y z (Pi.single i 1) k -
          (M₂ ω).gammaMap y z (Pi.single i 1) k) *
          (M₁ ω).gammaMap x y (Pi.single k 1) j +
        (M₂ ω).gammaMap y z (Pi.single i 1) k *
          ((M₁ ω).gammaMap x y (Pi.single k 1) j -
            (M₂ ω).gammaMap x y (Pi.single k 1) j))

end RegularityStructures

end
