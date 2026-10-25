/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovGammaDiffRelativeSource
public import Mathlib.Order.CompletePartialOrder

/-!
# Finite annular suprema for the mixed Gamma difference channels

The source estimate is applied after the Chen source has been split.  This
module contains the finite-cell bookkeeping; the pathwise `DΓ × DΓ` channel
is handled separately.
-/

@[expose] public noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal NNReal

namespace RegularityStructures

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝒯 : RegularityStructure ι}

omit [IsProbabilityMeasure P] in
theorem gammaDiffGoodLeftAnnulusStepSup_moment_le
    (S : Set ParabolicSpace)
    (M₁ M₂ : Ω → Model 𝒯 parabolicSemigroup)
    (D : Set (ι × ι)) (i j : ι) (N k p : ℕ) (hp : 1 ≤ p)
    (H : gammaCell S (k + 1) → gammaCell S (k + 1) → ℝ≥0∞)
    (hmeas : ∀ a b, AEMeasurable (fun ω => if parabolicNorm
      (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a) -
        hsParabolicCellRepresentative S (k + 1) b) ≤ 20 / (2 : ℝ) ^ N then
      ‖gammaDiffSplitLeftGoodTerm M₁ M₂ D i j
        (hsParabolicCellRepresentative S (k + 1) b)
        (hsParabolicCellRepresentative S (k + 1) a)
        (hsParabolicCellRepresentative S k
          (hsParabolicCellParent S k a)) ω‖ₑ else 0) P)
    (hterm : ∀ a b, ∫⁻ ω, (if parabolicNorm
      (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a) -
        hsParabolicCellRepresentative S (k + 1) b) ≤ 20 / (2 : ℝ) ^ N then
      ‖gammaDiffSplitLeftGoodTerm M₁ M₂ D i j
        (hsParabolicCellRepresentative S (k + 1) b)
        (hsParabolicCellRepresentative S (k + 1) a)
        (hsParabolicCellRepresentative S k
          (hsParabolicCellParent S k a)) ω‖ₑ else 0) ^ p ∂P ≤
      ⨆ u, ⨆ v, H u v) :
    ∫⁻ ω, gammaDiffGoodLeftAnnulusStepSup S M₁ M₂ D i j N k ω ^ p ∂P ≤
      (Fintype.card (gammaCell S (k + 1)) : ℝ≥0∞) ^ 2 *
        (⨆ a, ⨆ b, H a b) := by
  have hsup := finiteSup_lintegral_pow_le_card_mul
    (I := gammaCell S (k + 1) × gammaCell S (k + 1))
    (show p ≠ 0 by omega) (fun z => hmeas z.1 z.2)
      (fun z => hterm z.1 z.2)
  simpa only [gammaDiffGoodLeftAnnulusStepSup, iSup_prod,
    Fintype.card_prod, Nat.cast_mul, ENNReal.coe_mul, ENNReal.coe_pow,
    pow_two] using hsup

omit [IsProbabilityMeasure P] in
theorem gammaDiffGoodRightAnnulusStepSup_moment_le
    (S : Set ParabolicSpace)
    (M₁ M₂ : Ω → Model 𝒯 parabolicSemigroup)
    (D : Set (ι × ι)) (i j : ι) (N k p : ℕ) (hp : 1 ≤ p)
    (H : gammaCell S (k + 1) → gammaCell S (k + 1) → ℝ≥0∞)
    (hmeas : ∀ a b, AEMeasurable (fun ω => if parabolicNorm
      (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a) -
        hsParabolicCellRepresentative S (k + 1) b) ≤ 20 / (2 : ℝ) ^ N then
      ‖gammaDiffSplitRightGoodTerm M₁ M₂ D i j
        (hsParabolicCellRepresentative S k
          (hsParabolicCellParent S k a))
        (hsParabolicCellRepresentative S (k + 1) b)
        (hsParabolicCellRepresentative S k
          (hsParabolicCellParent S k b)) ω‖ₑ else 0) P)
    (hterm : ∀ a b, ∫⁻ ω, (if parabolicNorm
      (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a) -
        hsParabolicCellRepresentative S (k + 1) b) ≤ 20 / (2 : ℝ) ^ N then
      ‖gammaDiffSplitRightGoodTerm M₁ M₂ D i j
        (hsParabolicCellRepresentative S k
          (hsParabolicCellParent S k a))
        (hsParabolicCellRepresentative S (k + 1) b)
        (hsParabolicCellRepresentative S k
          (hsParabolicCellParent S k b)) ω‖ₑ else 0) ^ p ∂P ≤
      ⨆ u, ⨆ v, H u v) :
    ∫⁻ ω, gammaDiffGoodRightAnnulusStepSup S M₁ M₂ D i j N k ω ^ p ∂P ≤
      (Fintype.card (gammaCell S (k + 1)) : ℝ≥0∞) ^ 2 *
        (⨆ a, ⨆ b, H a b) := by
  have hsup := finiteSup_lintegral_pow_le_card_mul
    (I := gammaCell S (k + 1) × gammaCell S (k + 1))
    (show p ≠ 0 by omega) (fun z => hmeas z.1 z.2)
      (fun z => hterm z.1 z.2)
  simpa only [gammaDiffGoodRightAnnulusStepSup, iSup_prod,
    Fintype.card_prod, Nat.cast_mul, ENNReal.coe_mul, ENNReal.coe_pow,
    pow_two] using hsup

end RegularityStructures

end
