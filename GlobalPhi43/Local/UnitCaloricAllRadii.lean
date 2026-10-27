/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.UnitCaloricAffineError
public import GlobalPhi43.Local.PastAffineMonotonicity

/-! The actual unit caloric estimate on every testing radius up to one.
Large radii follow from monotonicity, with one constant before all data. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Set Metric
open scoped ContDiff ENNReal

 theorem exists_unit_caloric_all_radii : ∃ C > 0,
    ∀ (h : ParabolicSpace → ℝ) (O : Set ParabolicSpace), IsOpen O →
      unitHeatPastCarrier ⊆ O → ContDiffOn ℝ ∞ h O →
      ∀ F : ℝ, 0 ≤ F →
      (∀ p ∈ pastBall (0 : ParabolicSpace) 1, |sourceHeat h p| ≤ F) →
      ∀ R : ℝ, 0 ≤ R → R ≤ 1 →
        pastAffineError h 0 R ≤
          ENNReal.ofReal (C * ((pastAffineError h 0 1).toReal * R ^ 2 + F)) := by
  obtain ⟨C, hC, hb⟩ := exists_unit_caloric_affine_error
  refine ⟨max C 16, lt_of_lt_of_le hC (le_max_left _ _), ?_⟩
  intro h O hO hKO hh F hF hPDE R hR hRone
  have hE : 0 ≤ (pastAffineError h 0 1).toReal := ENNReal.toReal_nonneg
  have hterm : 0 ≤ (pastAffineError h 0 1).toReal * R ^ 2 + F := by positivity
  by_cases hs : R ≤ 1 / 4
  · exact (hb h O hO hKO hh F hF hPDE R hR hs).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hterm))
  · have hfin := unit_pastAffineError_ne_top h O hKO hh.continuousOn
    calc
      pastAffineError h 0 R ≤ pastAffineError h 0 1 := pastAffineError_mono h 0 hRone
      _ = ENNReal.ofReal (pastAffineError h 0 1).toReal := (ENNReal.ofReal_toReal hfin).symm
      _ ≤ ENNReal.ofReal (max C 16 * ((pastAffineError h 0 1).toReal * R ^ 2 + F)) := by
        apply ENNReal.ofReal_le_ofReal
        have hsq : 1 ≤ 16 * R ^ 2 := by nlinarith
        have he := mul_le_mul_of_nonneg_left hsq hE
        have hf : 0 ≤ 16 * F := by positivity
        have hc := mul_le_mul_of_nonneg_right (le_max_right C 16) hterm
        nlinarith

end GlobalPhi43.Local
