/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.KolmogorovHolderBesovCriterion
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Annealed closure of the dyadic holderBesov bound

This module turns the deterministic dyadic reduction into an explicit moment estimate.  The
endpoint moment assumptions are deliberately exposed: they are the output of the heat smoothing
estimate and Tonelli/Fubini for a random field.  This separation keeps measurability and tail
inputs visible in the theorem statement.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures

def dyadicHolderBesovTerm (η : ℝ) (n : ℕ) (f : C(Torus3, ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal ((dyadicScale n) ^ (-η / 2)) *
    ⨆ x : Torus3, ‖heatSemigroup (dyadicScale (n + 1)) f x‖ₑ

theorem holderBesovENorm_le_dyadicHolderBesovTerm_iSup {η : ℝ} (hη : η ≤ 0)
    (f : C(Torus3, ℝ)) :
    holderBesovENorm η f ≤ ⨆ n : ℕ, dyadicHolderBesovTerm η n f := by
  simpa only [dyadicHolderBesovTerm] using holderBesovENorm_le_dyadic_iSup hη f

theorem holderBesovENorm_natMoment_le_of_dyadic {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → C(Torus3, ℝ)} {η : ℝ} {p : ℕ} (hη : η ≤ 0)
    (hp : p ≠ 0)
    (_hholder : AEMeasurable (fun ω => holderBesovENorm η (X ω)) P)
    (hterm : ∀ n : ℕ,
      AEMeasurable (fun ω => dyadicHolderBesovTerm η n (X ω)) P)
    {b : ℕ → ℝ≥0∞}
    (hbound : ∀ n : ℕ,
      ∫⁻ ω, (dyadicHolderBesovTerm η n (X ω)) ^ p ∂P ≤ b n) :
    ∫⁻ ω, (holderBesovENorm η (X ω)) ^ p ∂P ≤ ∑' n, b n := by
  have hpoint : ∀ ω : Ω,
      (holderBesovENorm η (X ω)) ^ p ≤
        ∑' n : ℕ, (dyadicHolderBesovTerm η n (X ω)) ^ p := by
    intro ω
    have hle := holderBesovENorm_le_dyadicHolderBesovTerm_iSup hη (X ω)
    calc
      (holderBesovENorm η (X ω)) ^ p ≤
          (⨆ n : ℕ, dyadicHolderBesovTerm η n (X ω)) ^ p :=
        pow_le_pow_left' hle p
      _ = ⨆ n : ℕ, (dyadicHolderBesovTerm η n (X ω)) ^ p :=
        ENNReal.iSup_pow_of_ne_zero hp _
      _ ≤ ∑' n : ℕ, (dyadicHolderBesovTerm η n (X ω)) ^ p := by
        exact iSup_le fun n =>
          ENNReal.le_tsum (f := fun n : ℕ => (dyadicHolderBesovTerm η n (X ω)) ^ p) n
  have hmeas : ∀ n : ℕ,
      AEMeasurable (fun ω => (dyadicHolderBesovTerm η n (X ω)) ^ p) P := by
    intro n
    exact (hterm n).pow_const p
  calc
    ∫⁻ ω, (holderBesovENorm η (X ω)) ^ p ∂P ≤
        ∫⁻ ω, ∑' n : ℕ, (dyadicHolderBesovTerm η n (X ω)) ^ p ∂P :=
      lintegral_mono hpoint
    _ = ∑' n : ℕ, ∫⁻ ω, (dyadicHolderBesovTerm η n (X ω)) ^ p ∂P := by
      rw [lintegral_tsum hmeas]
    _ ≤ ∑' n : ℕ, b n := ENNReal.tsum_le_tsum hbound

end RegularityStructures

end
