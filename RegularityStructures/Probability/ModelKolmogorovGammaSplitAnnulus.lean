/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovGammaSplitSource
public import Mathlib.Order.CompletePartialOrder

/-!
# Annular envelopes for the split Gamma Chen source

The source split is lifted to the fixed-annulus finite nets.  The good
envelope retains a moment estimate; the bad envelope is reserved for the
pathwise geometric estimate in the completion module.
-/

@[expose] public noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal NNReal Topology

namespace RegularityStructures

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝒯 : RegularityStructure ι}

def gammaSplitLeftBadStepSupAnnulus
    (S : Set ParabolicSpace)
    (M : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (i j : ι) (N k : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ a : gammaCell S (k + 1), ⨆ b : gammaCell S (k + 1),
    if parabolicNorm
        (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a) -
          hsParabolicCellRepresentative S (k + 1) b) ≤ 20 / (2 : ℝ) ^ N then
      ‖gammaSplitLeftBadTerm (M ω) D i j
          (hsParabolicCellRepresentative S (k + 1) b)
          (hsParabolicCellRepresentative S (k + 1) a)
          (hsParabolicCellRepresentative S k
            (hsParabolicCellParent S k a))‖ₑ
    else 0

def gammaSplitRightBadStepSupAnnulus
    (S : Set ParabolicSpace)
    (M : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (i j : ι) (N k : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ a : gammaCell S (k + 1), ⨆ b : gammaCell S (k + 1),
    if parabolicNorm
        (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a) -
          hsParabolicCellRepresentative S (k + 1) b) ≤ 20 / (2 : ℝ) ^ N then
      ‖gammaSplitRightBadTerm (M ω) D i j
          (hsParabolicCellRepresentative S k
            (hsParabolicCellParent S k a))
          (hsParabolicCellRepresentative S k
            (hsParabolicCellParent S k b))
          (hsParabolicCellRepresentative S (k + 1) b)‖ₑ
    else 0

end RegularityStructures

end
