/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Tactic

/-!
# `q`-th moments of a square from `2q`-th moments

* `lintegral_enorm_sq_pow_le`: `E ‖f²‖^q = E ‖f‖^(2q) ≤ ofReal (D²)^q`;
* `lintegral_enorm_sq_sub_sq_pow_le`: `E ‖f² - g²‖^q ≤ ofReal (2 B D)^q` when
  `E ‖f - g‖^(2q) ≤ ofReal B ^ (2q)` and `E ‖f‖^(2q), E ‖g‖^(2q) ≤ ofReal D ^ (2q)`.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace RegularityStructures.Phi43

theorem lintegral_enorm_sq_pow_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f : Ω → ℝ}
    {q : ℕ} {D : ℝ} (hD : 0 ≤ D) (h : ∫⁻ ω, ‖f ω‖ₑ ^ (2 * q) ∂P ≤ ENNReal.ofReal D ^ (2 * q)) :
    ∫⁻ ω, ‖f ω ^ 2‖ₑ ^ q ∂P ≤ ENNReal.ofReal (D ^ 2) ^ q := by
  have e : ∀ ω, ‖f ω ^ 2‖ₑ ^ q = ‖f ω‖ₑ ^ (2 * q) := fun ω => by
    rw [enorm_pow, ← pow_mul]
  simp_rw [e]
  refine h.trans (le_of_eq ?_)
  rw [ENNReal.ofReal_pow hD, ← pow_mul]

theorem lintegral_enorm_sq_sub_sq_pow_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g) {q : ℕ} (hq : 1 ≤ q) {B D : ℝ}
    (hB : 0 ≤ B)
    (h1 : ∫⁻ ω, ‖f ω - g ω‖ₑ ^ (2 * q) ∂P ≤ ENNReal.ofReal B ^ (2 * q))
    (h2 : ∫⁻ ω, ‖f ω‖ₑ ^ (2 * q) ∂P ≤ ENNReal.ofReal D ^ (2 * q))
    (h3 : ∫⁻ ω, ‖g ω‖ₑ ^ (2 * q) ∂P ≤ ENNReal.ofReal D ^ (2 * q)) :
    ∫⁻ ω, ‖f ω ^ 2 - g ω ^ 2‖ₑ ^ q ∂P ≤ ENNReal.ofReal (2 * B * D) ^ q := by
  have hq0 : (1 : ℝ) ≤ ((2 * q : ℕ) : ℝ) := by
    have : 2 ≤ 2 * q := by omega
    exact_mod_cast (by omega : 1 ≤ 2 * q)
  -- the `L^(2q)` norm of the sum
  have hsum : ∫⁻ ω, ‖f ω + g ω‖ₑ ^ (2 * q) ∂P ≤ (2 * ENNReal.ofReal D) ^ (2 * q) := by
    have step : ∀ ω, ‖f ω + g ω‖ₑ ^ (2 * q) ≤
        2 ^ (2 * q - 1) * (‖f ω‖ₑ ^ (2 * q) + ‖g ω‖ₑ ^ (2 * q)) := by
      intro ω
      have h := ENNReal.rpow_add_le_mul_rpow_add_rpow ‖f ω‖ₑ ‖g ω‖ₑ hq0
      simp only [ENNReal.rpow_natCast] at h
      refine (pow_le_pow_left' (enorm_add_le _ _) _).trans (h.trans (le_of_eq ?_))
      congr 1
      have : ((2 * q : ℕ) : ℝ) - 1 = ((2 * q - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega)]; simp
      rw [this, ENNReal.rpow_natCast]
    calc ∫⁻ ω, ‖f ω + g ω‖ₑ ^ (2 * q) ∂P
        ≤ ∫⁻ ω, 2 ^ (2 * q - 1) * (‖f ω‖ₑ ^ (2 * q) + ‖g ω‖ₑ ^ (2 * q)) ∂P := lintegral_mono step
      _ = 2 ^ (2 * q - 1) * (∫⁻ ω, ‖f ω‖ₑ ^ (2 * q) ∂P + ∫⁻ ω, ‖g ω‖ₑ ^ (2 * q) ∂P) := by
          rw [lintegral_const_mul' _ _ (by simp), lintegral_add_left (hf.enorm.pow_const _)]
      _ ≤ 2 ^ (2 * q - 1) * (ENNReal.ofReal D ^ (2 * q) + ENNReal.ofReal D ^ (2 * q)) :=
          mul_le_mul_right (add_le_add h2 h3) _
      _ = (2 * ENNReal.ofReal D) ^ (2 * q) := by
          rw [← two_mul, ← mul_assoc, mul_pow]
          congr 1
          have : 2 * q = (2 * q - 1) + 1 := by omega
          conv_rhs => rw [this, pow_succ]
  have key : ∀ ω, ‖f ω ^ 2 - g ω ^ 2‖ₑ ^ q = ‖f ω - g ω‖ₑ ^ q * ‖f ω + g ω‖ₑ ^ q := by
    intro ω
    rw [← mul_pow, ← enorm_mul]
    congr 2
    ring
  simp_rw [key]
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq P Real.HolderConjugate.two_two
    (f := fun ω => ‖f ω - g ω‖ₑ ^ q) (g := fun ω => ‖f ω + g ω‖ₑ ^ q)
    (((hf.sub hg).enorm.pow_const q).aemeasurable) (((hf.add hg).enorm.pow_const q).aemeasurable)
  have e2 : ∀ (r : ℝ≥0∞), (r ^ q) ^ (2 : ℝ) = r ^ (2 * q) := by
    intro r
    rw [ENNReal.rpow_two, ← pow_mul, mul_comm]
  have e3 : ∀ (r : ℝ≥0∞), (r ^ (2 * q)) ^ (1 / (2 : ℝ)) = r ^ q := by
    intro r
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_natCast]
    congr 1
    push_cast
    ring
  simp only [Pi.mul_apply, e2] at hH
  calc ∫⁻ ω, ‖f ω - g ω‖ₑ ^ q * ‖f ω + g ω‖ₑ ^ q ∂P
      ≤ (∫⁻ ω, ‖f ω - g ω‖ₑ ^ (2 * q) ∂P) ^ (1 / (2 : ℝ)) *
        (∫⁻ ω, ‖f ω + g ω‖ₑ ^ (2 * q) ∂P) ^ (1 / (2 : ℝ)) := by simpa using hH
    _ ≤ (ENNReal.ofReal B ^ (2 * q)) ^ (1 / (2 : ℝ)) *
        ((2 * ENNReal.ofReal D) ^ (2 * q)) ^ (1 / (2 : ℝ)) :=
        mul_le_mul' (ENNReal.rpow_le_rpow h1 (by norm_num))
          (ENNReal.rpow_le_rpow hsum (by norm_num))
    _ = ENNReal.ofReal (2 * B * D) ^ q := by
        rw [e3, e3, ← mul_pow]
        congr 1
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num)]
        simp only [ENNReal.ofReal_ofNat]
        ring

end RegularityStructures.Phi43

end
