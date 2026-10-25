/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Tactic

/-!
# Minkowski and Hölder for the `q`-th moments in `lintegral` form

The moment hypotheses of the Kolmogorov bound for the model norms are phrased as
`∫⁻ ‖f ω‖ₑ ^ q ≤ ofReal b ^ q`. This module records the algebra of such bounds: sums, differences,
scalar multiples (Minkowski) and products (Cauchy–Schwarz, through the `2q`-th moments).
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem eLpNorm_nat_pow_eq_lintegral {f : Ω → ℝ} {q : ℕ} (hq : 1 ≤ q)
    (hf : AEStronglyMeasurable f P) :
    eLpNorm f (q : ENNReal) P ^ q = ∫⁻ ω, ‖f ω‖ₑ ^ q ∂P := by
  have hq0 : (q : ENNReal) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 (ENNReal.natCast_ne_top q) hf]
  simp only [ENNReal.toReal_natCast, ENNReal.rpow_natCast]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  have : (1 / (q : ℝ)) * (q : ℝ) = 1 := by
    have : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
    field_simp
  rw [this, ENNReal.rpow_one]

theorem eLpNorm_le_of_lintegral_le {f : Ω → ℝ} {q : ℕ} (hq : 1 ≤ q)
    (hf : AEStronglyMeasurable f P) {b : ENNReal}
    (h : ∫⁻ ω, ‖f ω‖ₑ ^ q ∂P ≤ b ^ q) : eLpNorm f (q : ENNReal) P ≤ b := by
  rw [← eLpNorm_nat_pow_eq_lintegral hq hf] at h
  exact (ENNReal.pow_le_pow_left_iff (by omega)).1 h

theorem lintegral_le_of_eLpNorm_le {f : Ω → ℝ} {q : ℕ} (hq : 1 ≤ q)
    (hf : AEStronglyMeasurable f P) {b : ENNReal}
    (h : eLpNorm f (q : ENNReal) P ≤ b) : ∫⁻ ω, ‖f ω‖ₑ ^ q ∂P ≤ b ^ q := by
  rw [← eLpNorm_nat_pow_eq_lintegral hq hf]
  exact pow_le_pow_left' h q

/-- **Minkowski for sums.** -/
theorem lintegral_enorm_pow_add_le {f g : Ω → ℝ} {q : ℕ} (hq : 1 ≤ q)
    (hf : AEStronglyMeasurable f P) (hg : AEStronglyMeasurable g P) {a b : ℝ}
    (hfa : ∫⁻ ω, ‖f ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal a ^ q)
    (hgb : ∫⁻ ω, ‖g ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal b ^ q) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∫⁻ ω, ‖f ω + g ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal (a + b) ^ q := by
  have h1 := eLpNorm_le_of_lintegral_le hq hf hfa
  have h2 := eLpNorm_le_of_lintegral_le hq hg hgb
  have hq1 : (1 : ENNReal) ≤ q := by exact_mod_cast hq
  have h3 : eLpNorm (f + g) (q : ENNReal) P ≤ ENNReal.ofReal (a + b) := by
    calc eLpNorm (f + g) (q : ENNReal) P ≤ eLpNorm f (q : ENNReal) P + eLpNorm g (q : ENNReal) P :=
          eLpNorm_add_le hq1
      _ ≤ ENNReal.ofReal a + ENNReal.ofReal b := add_le_add h1 h2
      _ = ENNReal.ofReal (a + b) := (ENNReal.ofReal_add ha hb).symm
  exact lintegral_le_of_eLpNorm_le hq (hf.add hg) h3

/-- **Minkowski for differences.** -/
theorem lintegral_enorm_pow_sub_le {f g : Ω → ℝ} {q : ℕ} (hq : 1 ≤ q)
    (hf : AEStronglyMeasurable f P) (hg : AEStronglyMeasurable g P) {a b : ℝ}
    (hfa : ∫⁻ ω, ‖f ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal a ^ q)
    (hgb : ∫⁻ ω, ‖g ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal b ^ q) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∫⁻ ω, ‖f ω - g ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal (a + b) ^ q := by
  have hgb' : ∫⁻ ω, ‖(-g) ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal b ^ q := by
    simpa [enorm_neg] using hgb
  have := lintegral_enorm_pow_add_le hq hf hg.neg hfa hgb' ha hb
  simpa [sub_eq_add_neg] using this

/-- **Scalar multiples.** -/
theorem lintegral_enorm_pow_const_mul_le {f : Ω → ℝ} {q : ℕ} (c : ℝ) {a : ℝ}
    (hfa : ∫⁻ ω, ‖f ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal a ^ q) :
    ∫⁻ ω, ‖c * f ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal (|c| * a) ^ q := by
  have e : ∀ ω, ‖c * f ω‖ₑ ^ q = ENNReal.ofReal |c| ^ q * ‖f ω‖ₑ ^ q := fun ω => by
    rw [enorm_mul, mul_pow, Real.enorm_eq_ofReal_abs]
  simp_rw [e]
  rw [lintegral_const_mul' _ _ (by simp)]
  calc ENNReal.ofReal |c| ^ q * ∫⁻ ω, ‖f ω‖ₑ ^ q ∂P
      ≤ ENNReal.ofReal |c| ^ q * ENNReal.ofReal a ^ q := by gcongr
    _ = ENNReal.ofReal (|c| * a) ^ q := by
      rw [← mul_pow, ENNReal.ofReal_mul (abs_nonneg c)]

/-- **Cauchy–Schwarz for products** through the `2q`-th moments. -/
theorem lintegral_enorm_pow_mul_le {f g : Ω → ℝ} {q : ℕ}
    (hf : AEMeasurable f P) (hg : AEMeasurable g P) {a b : ℝ}
    (hfa : ∫⁻ ω, ‖f ω‖ₑ ^ (2 * q) ∂P ≤ ENNReal.ofReal a ^ (2 * q))
    (hgb : ∫⁻ ω, ‖g ω‖ₑ ^ (2 * q) ∂P ≤ ENNReal.ofReal b ^ (2 * q)) (ha : 0 ≤ a) :
    ∫⁻ ω, ‖f ω * g ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal (a * b) ^ q := by
  have hF : AEMeasurable (fun ω => ‖f ω‖ₑ ^ q) P := hf.enorm.pow_const _
  have hG : AEMeasurable (fun ω => ‖g ω‖ₑ ^ q) P := hg.enorm.pow_const _
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P (p := 2) (q := 2) Real.HolderConjugate.two_two hF hG
  have e1 : ∀ (u : Ω → ℝ), ∫⁻ ω, (‖u ω‖ₑ ^ q) ^ (2 : ℝ) ∂P = ∫⁻ ω, ‖u ω‖ₑ ^ (2 * q) ∂P :=
    fun u => by
      refine lintegral_congr fun ω => ?_
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_natCast]
      congr 1
      push_cast
      ring
  have e2 : ∀ (c : ℝ), (ENNReal.ofReal c ^ (2 * q)) ^ (1 / (2 : ℝ)) = ENNReal.ofReal c ^ q := by
    intro c
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_natCast]
    congr 1
    push_cast
    ring
  simp only [Pi.mul_apply] at h
  rw [e1, e1] at h
  calc ∫⁻ ω, ‖f ω * g ω‖ₑ ^ q ∂P = ∫⁻ ω, ‖f ω‖ₑ ^ q * ‖g ω‖ₑ ^ q ∂P := by
        refine lintegral_congr fun ω => ?_
        rw [enorm_mul, mul_pow]
    _ ≤ (∫⁻ ω, ‖f ω‖ₑ ^ (2 * q) ∂P) ^ (1 / (2 : ℝ)) *
        (∫⁻ ω, ‖g ω‖ₑ ^ (2 * q) ∂P) ^ (1 / (2 : ℝ)) := h
    _ ≤ (ENNReal.ofReal a ^ (2 * q)) ^ (1 / (2 : ℝ)) *
        (ENNReal.ofReal b ^ (2 * q)) ^ (1 / (2 : ℝ)) := by
        gcongr
    _ = ENNReal.ofReal (a * b) ^ q := by
        rw [e2, e2, ← mul_pow, ENNReal.ofReal_mul ha]

/-- Monotonicity in the bound. -/
theorem lintegral_enorm_pow_mono {f : Ω → ℝ} {q : ℕ} {a b : ℝ}
    (h : ∫⁻ ω, ‖f ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal a ^ q) (hab : a ≤ b) :
    ∫⁻ ω, ‖f ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal b ^ q :=
  h.trans (pow_le_pow_left' (ENNReal.ofReal_le_ofReal hab) q)

/-- Monotonicity in the bound, for any enormous left side. -/
theorem le_ofReal_pow_mono {X : ENNReal} {q : ℕ} {a b : ℝ} (h : X ≤ ENNReal.ofReal a ^ q)
    (hab : a ≤ b) : X ≤ ENNReal.ofReal b ^ q :=
  h.trans (pow_le_pow_left' (ENNReal.ofReal_le_ofReal hab) q)

end RegularityStructures.Phi43

end
