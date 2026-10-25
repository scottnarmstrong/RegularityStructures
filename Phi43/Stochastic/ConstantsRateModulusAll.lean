/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsRateModulus
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Translation moduli for all shifts

A translation modulus valid for shifts of parabolic size at most one extends to all shifts for a
function in `Lᵖ`: for large shifts the trivial bound `‖f(· - h) - f‖ₚ ≤ 2 ‖f‖ₚ` suffices.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures.Phi43

theorem constantsRate_modulus_all {f : SpaceTime → ℝ} (hmeas : Measurable f) {q : ℝ}
    (hq : 1 ≤ q) (hf : MemLp f (ENNReal.ofReal q)) {C γ r₀ : ℝ} (hC : 0 ≤ C) (hγ : 0 ≤ γ)
    (hr₀ : 0 < r₀)
    (hmod : ∀ h : SpaceTime, 0 < torusParabolicSize h → torusParabolicSize h ≤ r₀ →
      ∫⁻ z, ‖f (z - h) - f z‖ₑ ^ q ≤ ENNReal.ofReal (C * torusParabolicSize h ^ γ)) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ h : SpaceTime, 0 < torusParabolicSize h →
      ∫⁻ z, ‖f (z - h) - f z‖ₑ ^ q ≤ ENNReal.ofReal (C' * torusParabolicSize h ^ γ) := by
  have hq0 : 0 < q := by linarith
  have hfin : ∫⁻ z, ‖f z‖ₑ ^ q < ⊤ := by
    have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (ENNReal.ofReal_pos.mpr hq0).ne' (by simp) hf.eLpNorm_lt_top
    simpa [ENNReal.toReal_ofReal hq0.le] using h
  let I : ℝ := (∫⁻ z, ‖f z‖ₑ ^ q).toReal
  have hI : 0 ≤ I := ENNReal.toReal_nonneg
  refine ⟨C + 2 ^ q * 2 * I / r₀ ^ γ, by positivity, ?_⟩
  intro h hr0
  by_cases hr1 : torusParabolicSize h ≤ r₀
  · refine (hmod h hr0 hr1).trans (ENNReal.ofReal_le_ofReal ?_)
    have : 0 ≤ 2 ^ q * 2 * I / r₀ ^ γ * torusParabolicSize h ^ γ := by positivity
    nlinarith
  · have hr1' : r₀ ≤ torusParabolicSize h := (not_le.mp hr1).le
    have hpt : ∀ z, ‖f (z - h) - f z‖ₑ ^ q ≤
        ENNReal.ofReal (2 ^ q) * (‖f (z - h)‖ₑ ^ q + ‖f z‖ₑ ^ q) := by
      intro z
      calc
        ‖f (z - h) - f z‖ₑ ^ q ≤ (‖f (z - h)‖ₑ + ‖f z‖ₑ) ^ q :=
          ENNReal.rpow_le_rpow enorm_sub_le hq0.le
        _ ≤ 2 ^ (q - 1) * (‖f (z - h)‖ₑ ^ q + ‖f z‖ₑ ^ q) :=
          ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hq
        _ ≤ _ := by
          gcongr
          rw [← ENNReal.ofReal_rpow_of_pos (by norm_num)]
          simp only [ENNReal.ofReal_ofNat]
          exact ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hshift : ∫⁻ z, ‖f (z - h)‖ₑ ^ q = ∫⁻ z, ‖f z‖ₑ ^ q :=
      lintegral_sub_right_eq_self (fun w => ‖f w‖ₑ ^ q) h
    calc
      ∫⁻ z, ‖f (z - h) - f z‖ₑ ^ q ≤
          ∫⁻ z, ENNReal.ofReal (2 ^ q) * (‖f (z - h)‖ₑ ^ q + ‖f z‖ₑ ^ q) :=
        lintegral_mono hpt
      _ = ENNReal.ofReal (2 ^ q) *
          ((∫⁻ z, ‖f (z - h)‖ₑ ^ q) + ∫⁻ z, ‖f z‖ₑ ^ q) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_add_left (f := fun z => ‖f (z - h)‖ₑ ^ q)
            ((hmeas.comp (measurable_id.sub_const h)).enorm.pow_const q)
            (fun z => ‖f z‖ₑ ^ q)]
      _ = ENNReal.ofReal (2 ^ q * 2 * I) := by
        rw [hshift, ← two_mul]
        have hI' : ∫⁻ z, ‖f z‖ₑ ^ q = ENNReal.ofReal I :=
          (ENNReal.ofReal_toReal hfin.ne).symm
        rw [hI', ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 ^ q * 2 by positivity),
          ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 ^ q by positivity), ENNReal.ofReal_ofNat,
          mul_assoc]
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have hrγ : 0 < r₀ ^ γ := by positivity
        have h1 : r₀ ^ γ ≤ torusParabolicSize h ^ γ := Real.rpow_le_rpow hr₀.le hr1' hγ
        have h2 : 0 ≤ 2 ^ q * 2 * I := by positivity
        have h3 : 2 ^ q * 2 * I ≤ 2 ^ q * 2 * I / r₀ ^ γ * torusParabolicSize h ^ γ := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hrγ]
          exact mul_le_mul_of_nonneg_left h1 h2
        nlinarith [h3, mul_nonneg hC (by positivity : (0 : ℝ) ≤ torusParabolicSize h ^ γ)]

end RegularityStructures.Phi43

end
