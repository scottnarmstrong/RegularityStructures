/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# Minkowski's inequality for kernel averages of random fields

For a kernel `k` on `Y` and a jointly measurable random field `F : Ω × Y → ℝ`,
`E ‖∫ k F‖^q ≤ (∫ ‖k‖)^(q-1) ∫ ‖k(y)‖ E‖F(y)‖^q dy`
(`lintegral_enorm_integral_mul_pow_le`), and in real form
`E ‖∫ k F‖^q ≤ ofReal (M₀^(q-1) M_q)` when `∫ |k| ≤ M₀` and `∫ |k(y)| B(y)^q ≤ M_q` with
`E ‖F(y)‖^q ≤ B(y)^q` (`lintegral_enorm_integral_mul_pow_le_of_bound`).
-/

public section

open MeasureTheory
open scoped ENNReal

namespace RegularityStructures.Phi43

/-- Hölder for a weight: `(∫ a b)^q ≤ (∫ a)^(q-1) ∫ a b^q`. -/
theorem lintegral_mul_pow_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {a b : α → ℝ≥0∞}
    (ha : AEMeasurable a μ) (hb : AEMeasurable b μ) {q : ℕ} (hq : 1 ≤ q) :
    (∫⁻ x, a x * b x ∂μ) ^ q ≤ (∫⁻ x, a x ∂μ) ^ (q - 1) * ∫⁻ x, a x * b x ^ q ∂μ := by
  rcases Nat.eq_or_lt_of_le hq with h1 | h2
  · subst h1
    simp
  · have hq1 : (1 : ℝ) < q := by exact_mod_cast h2
    have hq0 : (0 : ℝ) < q - 1 := by linarith
    set p : ℝ := (q : ℝ) / ((q : ℝ) - 1) with hp
    have hp1 : 1 < p := by rw [hp, lt_div_iff₀ hq0]; linarith
    have hinv : p⁻¹ + (q : ℝ)⁻¹ = 1 := by
      rw [hp]; field_simp; ring
    have hpq : p.HolderConjugate (q : ℝ) := Real.holderConjugate_iff.mpr ⟨hp1, hinv⟩
    have hp0 : 0 < p := by linarith
    have hqpos : (0 : ℝ) < q := by linarith
    have hf : AEMeasurable (fun x => a x ^ (1 / p)) μ := ha.pow_const _
    have hg : AEMeasurable (fun x => a x ^ (1 / (q : ℝ)) * b x) μ := (ha.pow_const _).mul hb
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf hg
    have e1 : ∀ x, (fun x => a x ^ (1 / p)) x * (fun x => a x ^ (1 / (q : ℝ)) * b x) x =
        a x * b x := by
      intro x
      simp only
      rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity)]
      have : 1 / p + 1 / (q : ℝ) = 1 := by rw [one_div, one_div]; exact hinv
      rw [this, ENNReal.rpow_one]
    have e2 : ∀ x, (a x ^ (1 / p)) ^ p = a x := by
      intro x
      rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
    have e3 : ∀ x, (a x ^ (1 / (q : ℝ)) * b x) ^ (q : ℝ) = a x * b x ^ q := by
      intro x
      rw [ENNReal.mul_rpow_of_nonneg _ _ hqpos.le, ← ENNReal.rpow_mul, one_div,
        inv_mul_cancel₀ hqpos.ne', ENNReal.rpow_one, ENNReal.rpow_natCast]
    simp only [Pi.mul_apply, e1, e2, e3] at h
    calc (∫⁻ x, a x * b x ∂μ) ^ q
        ≤ ((∫⁻ x, a x ∂μ) ^ (1 / p) * (∫⁻ x, a x * b x ^ q ∂μ) ^ (1 / (q : ℝ))) ^ q :=
          pow_le_pow_left' h q
      _ = (∫⁻ x, a x ∂μ) ^ (q - 1) * ∫⁻ x, a x * b x ^ q ∂μ := by
          rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
            ← ENNReal.rpow_mul, ← ENNReal.rpow_natCast, one_div, one_div,
            inv_mul_cancel₀ hqpos.ne', ENNReal.rpow_one]
          congr 2
          rw [hp]
          have : (q - 1 : ℕ) = (q : ℝ) - 1 := by
            rw [Nat.cast_sub hq]; simp
          rw [this]
          field_simp

/-- **Minkowski for kernel averages** (lintegral form). -/
theorem lintegral_enorm_integral_mul_pow_le {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    {P : Measure Ω} {μ : Measure Y} [SFinite P] [SFinite μ] {k : Y → ℝ} {F : Ω → Y → ℝ}
    (hk : Measurable k) (hF : Measurable fun z : Ω × Y => F z.1 z.2) {q : ℕ} (hq : 1 ≤ q) :
    ∫⁻ ω, ‖∫ y, k y * F ω y ∂μ‖ₑ ^ q ∂P ≤
      (∫⁻ y, ‖k y‖ₑ ∂μ) ^ (q - 1) * ∫⁻ y, ‖k y‖ₑ * ∫⁻ ω, ‖F ω y‖ₑ ^ q ∂P ∂μ := by
  have hFy : ∀ ω, Measurable (F ω) := fun ω => hF.comp measurable_prodMk_left
  have hG : Measurable fun z : Ω × Y => ‖k z.2‖ₑ * ‖F z.1 z.2‖ₑ ^ q :=
    (hk.comp measurable_snd).enorm.mul (hF.enorm.pow_const q)
  have step : ∀ ω, ‖∫ y, k y * F ω y ∂μ‖ₑ ^ q ≤
      (∫⁻ y, ‖k y‖ₑ ∂μ) ^ (q - 1) * ∫⁻ y, ‖k y‖ₑ * ‖F ω y‖ₑ ^ q ∂μ := by
    intro ω
    refine (pow_le_pow_left' ((enorm_integral_le_lintegral_enorm (fun y => k y * F ω y)).trans
      (le_of_eq (lintegral_congr fun y => enorm_mul _ _))) q).trans ?_
    exact lintegral_mul_pow_le (a := fun y => ‖k y‖ₑ) (b := fun y => ‖F ω y‖ₑ)
      hk.enorm.aemeasurable (hFy ω).enorm.aemeasurable hq
  refine (lintegral_mono step).trans ?_
  rw [lintegral_const_mul'' _ (hG.lintegral_prod_right'.aemeasurable)]
  refine mul_le_mul_right (le_of_eq ?_) _
  rw [lintegral_lintegral_swap hG.aemeasurable]
  refine lintegral_congr fun y => ?_
  have hFω : Measurable fun ω : Ω => F ω y := hF.comp (measurable_id.prodMk measurable_const)
  exact lintegral_const_mul'' (‖k y‖ₑ) (hFω.enorm.pow_const q).aemeasurable

/-- **Minkowski for kernel averages, real form.** -/
theorem lintegral_enorm_integral_mul_pow_le_of_bound {Ω Y : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Y] {P : Measure Ω} {μ : Measure Y} [SFinite P] [SFinite μ] {k : Y → ℝ}
    {F : Ω → Y → ℝ} (hk : Measurable k) (hki : Integrable k μ)
    (hF : Measurable fun z : Ω × Y => F z.1 z.2) {q : ℕ} (hq : 1 ≤ q) {B : Y → ℝ}
    (hB0 : ∀ y, 0 ≤ B y) (hB : ∀ y, ∫⁻ ω, ‖F ω y‖ₑ ^ q ∂P ≤ ENNReal.ofReal (B y) ^ q)
    {M₀ Mq : ℝ} (hM₀ : ∫ y, |k y| ∂μ ≤ M₀)
    (hBi : Integrable (fun y => |k y| * B y ^ q) μ) (hMq : ∫ y, |k y| * B y ^ q ∂μ ≤ Mq) :
    ∫⁻ ω, ‖∫ y, k y * F ω y ∂μ‖ₑ ^ q ∂P ≤ ENNReal.ofReal (M₀ ^ (q - 1) * Mq) := by
  refine (lintegral_enorm_integral_mul_pow_le hk hF hq).trans ?_
  have h0 : 0 ≤ M₀ := (integral_nonneg fun _ => abs_nonneg _).trans hM₀
  have e1 : ∫⁻ y, ‖k y‖ₑ ∂μ = ENNReal.ofReal (∫ y, |k y| ∂μ) := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm hki]
    simp only [Real.norm_eq_abs]
  have e2 : ∫⁻ y, ‖k y‖ₑ * ∫⁻ ω, ‖F ω y‖ₑ ^ q ∂P ∂μ ≤ ENNReal.ofReal (Mq) := by
    calc ∫⁻ y, ‖k y‖ₑ * ∫⁻ ω, ‖F ω y‖ₑ ^ q ∂P ∂μ
        ≤ ∫⁻ y, ‖k y‖ₑ * ENNReal.ofReal (B y) ^ q ∂μ :=
          lintegral_mono fun y => mul_le_mul_right (hB y) _
      _ = ∫⁻ y, ENNReal.ofReal (|k y| * B y ^ q) ∂μ := by
          refine lintegral_congr fun y => ?_
          rw [ENNReal.ofReal_mul (abs_nonneg _), ENNReal.ofReal_pow (hB0 y)]
          congr 1
          rw [← ofReal_norm, Real.norm_eq_abs]
      _ = ENNReal.ofReal (∫ y, |k y| * B y ^ q ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal hBi
            (Filter.Eventually.of_forall fun y => mul_nonneg (abs_nonneg _)
              (pow_nonneg (hB0 y) _))).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hMq
  calc (∫⁻ y, ‖k y‖ₑ ∂μ) ^ (q - 1) * ∫⁻ y, ‖k y‖ₑ * ∫⁻ ω, ‖F ω y‖ₑ ^ q ∂P ∂μ
      ≤ ENNReal.ofReal M₀ ^ (q - 1) * ENNReal.ofReal Mq := by
        rw [e1]
        exact mul_le_mul (pow_le_pow_left' (ENNReal.ofReal_le_ofReal hM₀) _) e2 zero_le zero_le
    _ = ENNReal.ofReal (M₀ ^ (q - 1) * Mq) := by
        rw [ENNReal.ofReal_mul (pow_nonneg h0 _), ENNReal.ofReal_pow h0]

end RegularityStructures.Phi43

end
