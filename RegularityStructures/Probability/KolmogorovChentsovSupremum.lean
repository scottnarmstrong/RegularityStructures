/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.KolmogorovChentsovApproximation
public import RegularityStructures.Probability.KolmogorovChentsovSupMoment
public import RegularityStructures.Probability.KolmogorovChentsovMomentClosure
public import Mathlib.Order.CompletePartialOrder

/-!
# The normalised dyadic supremum

The scale-wise estimates have a geometric sum when `p * r < q - 1`.  This
module packages that sum and records the resulting finite ENNReal moment.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace RegularityStructures

variable {Ω E : Type*} [MeasurableSpace Ω] [PseudoEMetricSpace E]
  {P : Measure Ω}

noncomputable def dyadicNormalisedSup (X : UnitInterval → Ω → E) (r : ℝ≥0)
    (ω : Ω) : ℝ≥0∞ :=
  ⨆ n, dyadicNormalised X r n ω

theorem dyadicBase_rpow_eq_geometric {γ : ℝ} (n : ℕ) :
    (dyadicBase n) ^ γ = (((2 : ℝ≥0∞)⁻¹) ^ γ) ^ n := by
  unfold dyadicBase
  calc
    (((2 : ℝ≥0∞)⁻¹) ^ n) ^ γ =
        (((2 : ℝ≥0∞)⁻¹) ^ (n : ℝ)) ^ γ := by
          rw [ENNReal.rpow_natCast]
    _ = ((2 : ℝ≥0∞)⁻¹) ^ ((n : ℝ) * γ) :=
      (ENNReal.rpow_mul _ _ _).symm
    _ = ((2 : ℝ≥0∞)⁻¹) ^ (γ * (n : ℝ)) := by rw [mul_comm]
    _ = (((2 : ℝ≥0∞)⁻¹) ^ γ) ^ (n : ℝ) := ENNReal.rpow_mul _ _ _
    _ = (((2 : ℝ≥0∞)⁻¹) ^ γ) ^ n := by rw [ENNReal.rpow_natCast]

theorem dyadicBase_rpow_tsum_ne_top {γ : ℝ} (hγ : 0 < γ) :
    (∑' n : ℕ, (dyadicBase n) ^ γ) ≠ ∞ := by
  have ha : ((2 : ℝ≥0∞)⁻¹) ^ γ < 1 :=
    ENNReal.rpow_lt_one (by norm_num) hγ
  rw [show (fun n : ℕ => (dyadicBase n) ^ γ) =
      (fun n : ℕ => (((2 : ℝ≥0∞)⁻¹) ^ γ) ^ n) by
        funext n; exact dyadicBase_rpow_eq_geometric n]
  rw [ENNReal.tsum_geometric]
  exact (ENNReal.inv_ne_top).2 (tsub_pos_iff_lt.mpr ha).ne'

theorem dyadicNormalised_aemeasurable (X : UnitInterval → Ω → E)
    (r : ℝ≥0)
    (hmeas : ∀ s t, AEMeasurable (fun ω => edist (X s ω) (X t ω)) P)
    (n : ℕ) : AEMeasurable (dyadicNormalised X r n) P := by
  unfold dyadicNormalised
  exact (dyadicCloseSup_aemeasurable X hmeas n).mul_const _

theorem dyadicNormalisedSup_aemeasurable (X : UnitInterval → Ω → E)
    (r : ℝ≥0)
    (hmeas : ∀ s t, AEMeasurable (fun ω => edist (X s ω) (X t ω)) P) :
    AEMeasurable (dyadicNormalisedSup X r) P := by
  unfold dyadicNormalisedSup
  apply AEMeasurable.iSup
  intro n
  exact dyadicNormalised_aemeasurable X r hmeas n

theorem dyadicNormalisedSup_lintegral_pow_le {p : ℕ} {q : ℝ} {M : ℝ≥0∞}
    {r : ℝ≥0} (hp : 1 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hpr : (p : ℝ) * (r : ℝ) < q - 1)
    (X : UnitInterval → Ω → E)
    (hmeas : ∀ s t, AEMeasurable (fun ω => edist (X s ω) (X t ω)) P)
    (hpair : ∀ s t, ∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P ≤
      M * edist s t ^ q) :
    ∫⁻ ω, dyadicNormalisedSup X r ω ^ p ∂P ≤
      (10 : ℝ≥0∞) * M * (4 : ℝ≥0∞) ^ q *
        ∑' n : ℕ, (dyadicBase n) ^ (q - (p : ℝ) * (r : ℝ) - 1) := by
  have hgamma : 0 < q - (p : ℝ) * (r : ℝ) - 1 := by linarith
  have hterm : ∀ n, ∫⁻ ω, dyadicNormalised X r n ω ^ p ∂P ≤
      (10 : ℝ≥0∞) * M * (4 : ℝ≥0∞) ^ q *
        (dyadicBase n) ^ (q - (p : ℝ) * (r : ℝ) - 1) := by
    intro n
    exact dyadicNormalised_lintegral_pow_le hp hq hr hpr X hmeas hpair n
  calc
    ∫⁻ ω, dyadicNormalisedSup X r ω ^ p ∂P ≤
        ∑' n : ℕ, ∫⁻ ω, dyadicNormalised X r n ω ^ p ∂P := by
      apply lintegral_iSup_pow_le_tsum_lintegral_pow hp
      intro n
      exact dyadicNormalised_aemeasurable X r hmeas n
    _ ≤ ∑' n : ℕ, (10 : ℝ≥0∞) * M * (4 : ℝ≥0∞) ^ q *
        (dyadicBase n) ^ (q - (p : ℝ) * (r : ℝ) - 1) :=
      ENNReal.tsum_le_tsum hterm
    _ = (10 : ℝ≥0∞) * M * (4 : ℝ≥0∞) ^ q *
        ∑' n : ℕ, (dyadicBase n) ^ (q - (p : ℝ) * (r : ℝ) - 1) := by
      rw [ENNReal.tsum_mul_left]

theorem dyadicNormalisedSup_lintegral_pow_lt_top {p : ℕ} {q : ℝ} {M : ℝ≥0∞}
    {r : ℝ≥0} (hp : 1 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hpr : (p : ℝ) * (r : ℝ) < q - 1) (hM : M ≠ ∞)
    (X : UnitInterval → Ω → E)
    (hmeas : ∀ s t, AEMeasurable (fun ω => edist (X s ω) (X t ω)) P)
    (hpair : ∀ s t, ∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P ≤
      M * edist s t ^ q) :
    ∫⁻ ω, dyadicNormalisedSup X r ω ^ p ∂P < ∞ := by
  have hle := dyadicNormalisedSup_lintegral_pow_le hp hq hr hpr X hmeas hpair
  have hsum : (∑' n : ℕ, (dyadicBase n) ^
      (q - (p : ℝ) * (r : ℝ) - 1)) ≠ ∞ :=
    dyadicBase_rpow_tsum_ne_top (by linarith)
  have hC : (10 : ℝ≥0∞) * M * (4 : ℝ≥0∞) ^ q < ∞ := by
    apply ENNReal.mul_lt_top
    · apply ENNReal.mul_lt_top
      · simp
      · exact (lt_top_iff_ne_top.mpr hM)
    · exact ENNReal.rpow_lt_top_of_nonneg hq ENNReal.coe_ne_top
  apply lt_of_le_of_lt hle
  exact ENNReal.mul_lt_top hC (lt_top_iff_ne_top.mpr hsum)

end RegularityStructures

end
