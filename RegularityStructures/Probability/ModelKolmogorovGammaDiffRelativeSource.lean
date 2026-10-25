/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovGammaDiffGoodMoment
public import Mathlib.Order.CompletePartialOrder

/-!
# Split annular sources for the two-model Gamma difference

The annular increment is split before any supremum or moment estimate. The good term is the
complement of `DΓ × DΓ`; the bad term is the finite pathwise sector. This is the algebra on the side
of the source bounds in the Kolmogorov criterion for models.
-/

@[expose] public noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal NNReal

namespace RegularityStructures

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝒯 : RegularityStructure ι}

def gammaDiffGoodLeftAnnulusStepSup
    (S : Set ParabolicSpace)
    (M₁ M₂ : Ω → Model 𝒯 parabolicSemigroup)
    (D : Set (ι × ι)) (i j : ι) (N k : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ a : gammaCell S (k + 1), ⨆ b : gammaCell S (k + 1),
    if parabolicNorm
        (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a) -
          hsParabolicCellRepresentative S (k + 1) b) ≤ 20 / (2 : ℝ) ^ N then
      ‖gammaDiffSplitLeftGoodTerm M₁ M₂ D i j
          (hsParabolicCellRepresentative S (k + 1) b)
          (hsParabolicCellRepresentative S (k + 1) a)
          (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a)) ω‖ₑ
    else 0

def gammaDiffBadLeftAnnulusStepSup
    (S : Set ParabolicSpace)
    (M₁ M₂ : Ω → Model 𝒯 parabolicSemigroup)
    (D : Set (ι × ι)) (i j : ι) (N k : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ a : gammaCell S (k + 1), ⨆ b : gammaCell S (k + 1),
    if parabolicNorm
        (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a) -
          hsParabolicCellRepresentative S (k + 1) b) ≤ 20 / (2 : ℝ) ^ N then
      ‖gammaSplitLeftBadTermDiff (M₁ ω) (M₂ ω) D i j
          (hsParabolicCellRepresentative S (k + 1) b)
          (hsParabolicCellRepresentative S (k + 1) a)
          (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a))‖ₑ
    else 0

def gammaDiffGoodRightAnnulusStepSup
    (S : Set ParabolicSpace)
    (M₁ M₂ : Ω → Model 𝒯 parabolicSemigroup)
    (D : Set (ι × ι)) (i j : ι) (N k : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ a : gammaCell S (k + 1), ⨆ b : gammaCell S (k + 1),
    if parabolicNorm
        (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a) -
          hsParabolicCellRepresentative S (k + 1) b) ≤ 20 / (2 : ℝ) ^ N then
      ‖gammaDiffSplitRightGoodTerm M₁ M₂ D i j
          (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a))
          (hsParabolicCellRepresentative S (k + 1) b)
          (hsParabolicCellRepresentative S k (hsParabolicCellParent S k b)) ω‖ₑ
    else 0

def gammaDiffBadRightAnnulusStepSup
    (S : Set ParabolicSpace)
    (M₁ M₂ : Ω → Model 𝒯 parabolicSemigroup)
    (D : Set (ι × ι)) (i j : ι) (N k : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ a : gammaCell S (k + 1), ⨆ b : gammaCell S (k + 1),
    if parabolicNorm
        (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a) -
          hsParabolicCellRepresentative S (k + 1) b) ≤ 20 / (2 : ℝ) ^ N then
      ‖gammaSplitRightBadTermDiff (M₁ ω) (M₂ ω) D i j
          (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a))
          (hsParabolicCellRepresentative S (k + 1) b)
          (hsParabolicCellRepresentative S k (hsParabolicCellParent S k b))‖ₑ
    else 0

omit [MeasurableSpace Ω] in
private theorem gammaDiffAnnulusSplitLeftPointwise
    (S : Set ParabolicSpace)
    (M₁ M₂ : Ω → Model 𝒯 parabolicSemigroup)
    (D : Set (ι × ι)) (i j : ι) (N k : ℕ) (ω : Ω)
    (a b : gammaCell S (k + 1)) (hij : 𝒯.deg j < 𝒯.deg i) :
    (if parabolicNorm
        (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a) -
          hsParabolicCellRepresentative S (k + 1) b) ≤ 20 / (2 : ℝ) ^ N then
      ‖(M₁ ω).gammaMap
          (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a))
          (hsParabolicCellRepresentative S (k + 1) b)
          (Pi.single i 1) j -
        (M₂ ω).gammaMap
          (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a))
          (hsParabolicCellRepresentative S (k + 1) b)
          (Pi.single i 1) j -
        ((M₁ ω).gammaMap
          (hsParabolicCellRepresentative S (k + 1) a)
          (hsParabolicCellRepresentative S (k + 1) b)
          (Pi.single i 1) j -
        (M₂ ω).gammaMap
          (hsParabolicCellRepresentative S (k + 1) a)
          (hsParabolicCellRepresentative S (k + 1) b)
          (Pi.single i 1) j)‖ₑ
    else 0) ≤
      gammaDiffGoodLeftAnnulusStepSup S M₁ M₂ D i j N k ω +
        gammaDiffBadLeftAnnulusStepSup S M₁ M₂ D i j N k ω := by
  by_cases hnear : parabolicNorm
      (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a) -
        hsParabolicCellRepresentative S (k + 1) b) ≤ 20 / (2 : ℝ) ^ N
  · simp only [ite_eq_left hnear]
    have hEq := gammaDiffSplitLeftTerm_eq M₁ M₂ D i j
      (hsParabolicCellRepresentative S (k + 1) b)
      (hsParabolicCellRepresentative S (k + 1) a)
      (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a)) ω hij
    calc
      _ = ‖gammaDiffSplitLeftGoodTerm M₁ M₂ D i j
          (hsParabolicCellRepresentative S (k + 1) b)
          (hsParabolicCellRepresentative S (k + 1) a)
          (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a)) ω +
          gammaSplitLeftBadTermDiff (M₁ ω) (M₂ ω) D i j
            (hsParabolicCellRepresentative S (k + 1) b)
            (hsParabolicCellRepresentative S (k + 1) a)
            (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a))‖ₑ := by rw [← hEq]
      _ ≤ ‖gammaDiffSplitLeftGoodTerm M₁ M₂ D i j
          (hsParabolicCellRepresentative S (k + 1) b)
          (hsParabolicCellRepresentative S (k + 1) a)
          (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a)) ω‖ₑ +
          ‖gammaSplitLeftBadTermDiff (M₁ ω) (M₂ ω) D i j
            (hsParabolicCellRepresentative S (k + 1) b)
            (hsParabolicCellRepresentative S (k + 1) a)
            (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a))‖ₑ := enorm_add_le _ _
      _ ≤ gammaDiffGoodLeftAnnulusStepSup S M₁ M₂ D i j N k ω +
          gammaDiffBadLeftAnnulusStepSup S M₁ M₂ D i j N k ω := by
        exact add_le_add
          (le_iSup_of_le a (le_iSup_of_le b (by simp [hnear])))
          (le_iSup_of_le a (le_iSup_of_le b (by simp [hnear])))
  · simp only [ite_eq_right hnear, zero_le]

omit [MeasurableSpace Ω] in
private theorem gammaDiffAnnulusSplitRightPointwise
    (S : Set ParabolicSpace)
    (M₁ M₂ : Ω → Model 𝒯 parabolicSemigroup)
    (D : Set (ι × ι)) (i j : ι) (N k : ℕ) (ω : Ω)
    (a b : gammaCell S (k + 1)) (hij : 𝒯.deg j < 𝒯.deg i) :
    (if parabolicNorm
        (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a) -
          hsParabolicCellRepresentative S (k + 1) b) ≤ 20 / (2 : ℝ) ^ N then
      ‖(M₁ ω).gammaMap
          (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a))
          (hsParabolicCellRepresentative S k (hsParabolicCellParent S k b))
          (Pi.single i 1) j -
        (M₂ ω).gammaMap
          (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a))
          (hsParabolicCellRepresentative S k (hsParabolicCellParent S k b))
          (Pi.single i 1) j -
        ((M₁ ω).gammaMap
          (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a))
          (hsParabolicCellRepresentative S (k + 1) b)
          (Pi.single i 1) j -
        (M₂ ω).gammaMap
          (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a))
          (hsParabolicCellRepresentative S (k + 1) b)
          (Pi.single i 1) j)‖ₑ
    else 0) ≤
      gammaDiffGoodRightAnnulusStepSup S M₁ M₂ D i j N k ω +
        gammaDiffBadRightAnnulusStepSup S M₁ M₂ D i j N k ω := by
  by_cases hnear : parabolicNorm
      (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a) -
        hsParabolicCellRepresentative S (k + 1) b) ≤ 20 / (2 : ℝ) ^ N
  · simp only [ite_eq_left hnear]
    have hEq := gammaDiffSplitRightTerm_eq M₁ M₂ D i j
      (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a))
      (hsParabolicCellRepresentative S (k + 1) b)
      (hsParabolicCellRepresentative S k (hsParabolicCellParent S k b)) ω hij
    calc
      _ = ‖gammaDiffSplitRightGoodTerm M₁ M₂ D i j
          (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a))
          (hsParabolicCellRepresentative S (k + 1) b)
          (hsParabolicCellRepresentative S k (hsParabolicCellParent S k b)) ω +
          gammaSplitRightBadTermDiff (M₁ ω) (M₂ ω) D i j
            (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a))
            (hsParabolicCellRepresentative S (k + 1) b)
            (hsParabolicCellRepresentative S k (hsParabolicCellParent S k b))‖ₑ := by rw [← hEq]
      _ ≤ ‖gammaDiffSplitRightGoodTerm M₁ M₂ D i j
          (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a))
          (hsParabolicCellRepresentative S (k + 1) b)
          (hsParabolicCellRepresentative S k (hsParabolicCellParent S k b)) ω‖ₑ +
          ‖gammaSplitRightBadTermDiff (M₁ ω) (M₂ ω) D i j
            (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a))
            (hsParabolicCellRepresentative S (k + 1) b)
            (hsParabolicCellRepresentative S k (hsParabolicCellParent S k b))‖ₑ := enorm_add_le _ _
      _ ≤ gammaDiffGoodRightAnnulusStepSup S M₁ M₂ D i j N k ω +
          gammaDiffBadRightAnnulusStepSup S M₁ M₂ D i j N k ω := by
        exact add_le_add
          (le_iSup_of_le a (le_iSup_of_le b (by simp [hnear])))
          (le_iSup_of_le a (le_iSup_of_le b (by simp [hnear])))
  · simp only [ite_eq_right hnear, zero_le]

omit [MeasurableSpace Ω] in
theorem gammaDiffAnnulusSplitLeftStep_le
    (S : Set ParabolicSpace)
    (M₁ M₂ : Ω → Model 𝒯 parabolicSemigroup)
    (D : Set (ι × ι)) (i j : ι) (N k : ℕ) (ω : Ω)
    (hij : 𝒯.deg j < 𝒯.deg i) :
    gammaProductLeftStepSupAnnulus S
        (fun x y ω => (M₁ ω).gammaMap x y (Pi.single i 1) j -
          (M₂ ω).gammaMap x y (Pi.single i 1) j) N k ω ≤
      gammaDiffGoodLeftAnnulusStepSup S M₁ M₂ D i j N k ω +
        gammaDiffBadLeftAnnulusStepSup S M₁ M₂ D i j N k ω := by
  unfold gammaProductLeftStepSupAnnulus
  refine iSup_le (fun a => iSup_le (fun b =>
    gammaDiffAnnulusSplitLeftPointwise S M₁ M₂ D i j N k ω a b hij))

omit [MeasurableSpace Ω] in
theorem gammaDiffAnnulusSplitRightStep_le
    (S : Set ParabolicSpace)
    (M₁ M₂ : Ω → Model 𝒯 parabolicSemigroup)
    (D : Set (ι × ι)) (i j : ι) (N k : ℕ) (ω : Ω)
    (hij : 𝒯.deg j < 𝒯.deg i) :
    gammaProductRightStepSupAnnulus S
        (fun x y ω => (M₁ ω).gammaMap x y (Pi.single i 1) j -
          (M₂ ω).gammaMap x y (Pi.single i 1) j) N k ω ≤
      gammaDiffGoodRightAnnulusStepSup S M₁ M₂ D i j N k ω +
        gammaDiffBadRightAnnulusStepSup S M₁ M₂ D i j N k ω := by
  unfold gammaProductRightStepSupAnnulus
  refine iSup_le (fun a => iSup_le (fun b =>
    gammaDiffAnnulusSplitRightPointwise S M₁ M₂ D i j N k ω a b hij))

end RegularityStructures

end
