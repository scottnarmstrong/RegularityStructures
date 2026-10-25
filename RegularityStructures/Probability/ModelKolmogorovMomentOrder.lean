/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs

/-!
# Lower moment orders on a probability space

This is the Lyapunov step used when several finite-sector Gamma estimates are
proved at one large moment order.  It is deliberately stated for real-valued
fields and does not package any model-specific hypotheses.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace RegularityStructures

theorem lintegral_enorm_pow_le_of_nat_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {f : Ω → ℝ} (hf : AEMeasurable f P) {p q : ℕ} (hp : 1 ≤ p) (hpq : p ≤ q)
    {A : ℝ≥0∞} (hA : ∫⁻ ω, ‖f ω‖ₑ ^ q ∂P ≤ A ^ q) :
    ∫⁻ ω, ‖f ω‖ₑ ^ p ∂P ≤ A ^ p := by
  have hp0 : (p : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hp)
  have hq0 : (q : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (hp.trans hpq))
  have hpTop : (p : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  have hqTop : (q : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  have hnorm : eLpNorm f (p : ℝ≥0∞) P ≤ eLpNorm f (q : ℝ≥0∞) P := by
    apply eLpNorm_le_eLpNorm_of_exponent_le
    exact_mod_cast hpq
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpTop hf.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqTop hf.aestronglyMeasurable] at hnorm
  have hpcast : (p : ℝ≥0∞).toReal = p := by simp
  have hqcast : (q : ℝ≥0∞).toReal = q := by simp
  rw [hpcast, hqcast] at hnorm
  have hnorm' :
      (∫⁻ ω, ‖f ω‖ₑ ^ p ∂P) ^ (1 / (p : ℝ)) ≤
        (A ^ q) ^ (1 / (q : ℝ)) := by
    calc
      (∫⁻ ω, ‖f ω‖ₑ ^ p ∂P) ^ (1 / (p : ℝ)) ≤
          (∫⁻ ω, ‖f ω‖ₑ ^ q ∂P) ^ (1 / (q : ℝ)) := by
        simpa only [ENNReal.rpow_natCast] using hnorm
      _ ≤ (A ^ q) ^ (1 / (q : ℝ)) := by
        exact ENNReal.rpow_le_rpow hA (by positivity)
  have hpow : (A ^ q) ^ (1 / (q : ℝ)) = A := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    have hqpos : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hp.trans hpq))
    field_simp
    simp
  rw [hpow] at hnorm'
  have hfinal := ENNReal.rpow_le_rpow hnorm' (by positivity : (0 : ℝ) ≤ (p : ℝ))
  rw [← ENNReal.rpow_mul] at hfinal
  have hpcancel : (1 / (p : ℝ)) * (p : ℝ) = 1 := by
    field_simp
  rw [hpcancel, ENNReal.rpow_one] at hfinal
  simpa only [ENNReal.rpow_natCast] using hfinal

end RegularityStructures

end
