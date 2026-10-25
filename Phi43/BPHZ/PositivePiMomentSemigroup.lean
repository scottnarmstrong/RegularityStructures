/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.PositivePiMomentMinkowski
public import Phi43.BPHZ.SemigroupTestPeriodise
import Mathlib.Tactic

/-!
# Minkowski for the parabolic semigroup

If `E ‖F(y)‖^q ≤ (C₀ ‖y - x‖_𝔰^s)^q` for all `y`, then
`E ‖(Q_t F)(x)‖^q ≤ (C t^(s/4))^q` for every `t > 0`, with `C` depending only on `q, s, C₀`
(`lintegral_enorm_semigroup_apply_pow_le`).
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **Minkowski for the parabolic semigroup.** -/
theorem lintegral_enorm_semigroup_apply_pow_le {q : ℕ} (hq : 1 ≤ q) {s : ℝ} (hs : 0 ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {C₀ : ℝ}, 0 ≤ C₀ → ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      [SFinite P] {F : Ω → ParabolicSpace → ℝ} (x : ParabolicSpace),
      (Measurable fun z : Ω × ParabolicSpace => F z.1 z.2) →
      (∀ y, ∫⁻ ω, ‖F ω y‖ₑ ^ q ∂P ≤
        ENNReal.ofReal (C₀ * parabolicSemigroup.scaleDist y x ^ s) ^ q) →
      ∀ {t : ℝ}, 0 < t →
        ∫⁻ ω, ‖∫ y, parabolicSemigroup.kernel t x y * F ω y‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * C₀ * t ^ (s / 4)) ^ q := by
  set M₀ : ℝ := parabolicSemigroup.momentConst 0 with hM₀
  set Mq : ℝ := parabolicSemigroup.momentConst (s * q) with hMq
  have hM₀0 : 0 ≤ M₀ := parabolicSemigroup.momentConst_nonneg 0
  have hMq0 : 0 ≤ Mq := parabolicSemigroup.momentConst_nonneg _
  set X : ℝ := M₀ ^ (q - 1) * Mq with hX
  have hX0 : 0 ≤ X := by positivity
  refine ⟨X ^ ((1 : ℝ) / q), by positivity, ?_⟩
  intro C₀ hC₀ Ω _ P _ F x hF hB t ht
  have hk : Measurable (fun y : ParabolicSpace => parabolicSemigroup.kernel t x y) :=
    measurable_parabolicSemigroup_kernel t x
  have hki : Integrable (fun y : ParabolicSpace => parabolicSemigroup.kernel t x y) := by
    have := parabolicSemigroup.integrable_moment ht (le_refl (0 : ℝ)) x
    refine (integrable_norm_iff hk.aestronglyMeasurable).1 ?_
    simpa using this
  have hB0 : ∀ y, 0 ≤ C₀ * parabolicSemigroup.scaleDist y x ^ s := fun y =>
    mul_nonneg hC₀ (Real.rpow_nonneg (parabolicSemigroup.scaleDist_nonneg y x) _)
  have hpow : ∀ y, (C₀ * parabolicSemigroup.scaleDist y x ^ s) ^ q =
      C₀ ^ q * parabolicSemigroup.scaleDist y x ^ (s * q) := by
    intro y
    rw [mul_pow, ← Real.rpow_natCast (parabolicSemigroup.scaleDist y x ^ s) q,
      ← Real.rpow_mul (parabolicSemigroup.scaleDist_nonneg y x)]
  have hint : Integrable (fun y => |parabolicSemigroup.kernel t x y| *
      (C₀ * parabolicSemigroup.scaleDist y x ^ s) ^ q) := by
    have := (parabolicSemigroup.integrable_moment ht (r := s * q) (by positivity) x).const_mul
      (C₀ ^ q)
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [hpow]
    ring
  have h1 : ∫ y, |parabolicSemigroup.kernel t x y| ≤ M₀ := by
    have := parabolicSemigroup.moment_le ht (le_refl (0 : ℝ)) x
    simpa [hM₀] using this
  have h2 : ∫ y, |parabolicSemigroup.kernel t x y| *
      (C₀ * parabolicSemigroup.scaleDist y x ^ s) ^ q ≤ C₀ ^ q * Mq * t ^ (s * q / 4) := by
    have hm := parabolicSemigroup.moment_le ht (r := s * q) (by positivity) x
    have : ∫ y, |parabolicSemigroup.kernel t x y| *
        (C₀ * parabolicSemigroup.scaleDist y x ^ s) ^ q =
        C₀ ^ q * ∫ y, |parabolicSemigroup.kernel t x y| *
          parabolicSemigroup.scaleDist y x ^ (s * q) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [hpow]
      ring
    rw [this]
    have hq4 : parabolicSemigroup.order = 4 := rfl
    rw [hq4] at hm
    calc C₀ ^ q * ∫ y, |parabolicSemigroup.kernel t x y| *
          parabolicSemigroup.scaleDist y x ^ (s * q)
        ≤ C₀ ^ q * (Mq * t ^ (s * q / 4)) := mul_le_mul_of_nonneg_left hm (by positivity)
      _ = _ := by ring
  have key := lintegral_enorm_integral_mul_pow_le_of_bound (P := P) hk hki hF hq hB0 hB h1 hint h2
  refine key.trans (le_of_eq ?_)
  have htq : (t ^ (s / 4)) ^ q = t ^ (s * q / 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    congr 1
    ring
  have hXq : (X ^ ((1 : ℝ) / q)) ^ q = X := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX0, one_div, inv_mul_cancel₀ (by positivity),
      Real.rpow_one]
  rw [← ENNReal.ofReal_pow (by positivity), mul_pow, mul_pow, hXq, htq]
  congr 1
  rw [hX]
  ring

private theorem add_pow_le_two_pow_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (q : ℕ) :
    (a + b) ^ q ≤ 2 ^ q * (a ^ q + b ^ q) := by
  rcases le_total a b with h | h
  · calc (a + b) ^ q ≤ (2 * b) ^ q := pow_le_pow_left₀ (by positivity) (by linarith) q
      _ = 2 ^ q * b ^ q := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [pow_nonneg ha q]) (by positivity)
  · calc (a + b) ^ q ≤ (2 * a) ^ q := pow_le_pow_left₀ (by positivity) (by linarith) q
      _ = 2 ^ q * a ^ q := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [pow_nonneg hb q]) (by positivity)

/-- **Minkowski for the parabolic semigroup, two-power bound.**  If
`E ‖F(y)‖^q ≤ (C₀ (d^s + d^m))^q` with `s ≤ m`, then for `t ∈ (0, 1]`,
`E ‖(Q_t F)(x)‖^q ≤ (C C₀ t^(s/4))^q`. -/
theorem lintegral_enorm_semigroup_apply_pow_le_two {q : ℕ} (hq : 1 ≤ q) {s m : ℝ} (hs : 0 ≤ s)
    (hsm : s ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {C₀ : ℝ}, 0 ≤ C₀ → ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      [SFinite P] {F : Ω → ParabolicSpace → ℝ} (x : ParabolicSpace),
      (Measurable fun z : Ω × ParabolicSpace => F z.1 z.2) →
      (∀ y, ∫⁻ ω, ‖F ω y‖ₑ ^ q ∂P ≤ ENNReal.ofReal (C₀ * (parabolicSemigroup.scaleDist y x ^ s +
        parabolicSemigroup.scaleDist y x ^ m)) ^ q) →
      ∀ {t : ℝ}, 0 < t → t ≤ 1 →
        ∫⁻ ω, ‖∫ y, parabolicSemigroup.kernel t x y * F ω y‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * C₀ * t ^ (s / 4)) ^ q := by
  set M₀ : ℝ := parabolicSemigroup.momentConst 0 with hM₀
  set Ms : ℝ := parabolicSemigroup.momentConst (s * q) with hMs
  set Mm : ℝ := parabolicSemigroup.momentConst (m * q) with hMm
  have hM₀0 : 0 ≤ M₀ := parabolicSemigroup.momentConst_nonneg 0
  have hMs0 : 0 ≤ Ms := parabolicSemigroup.momentConst_nonneg _
  have hMm0 : 0 ≤ Mm := parabolicSemigroup.momentConst_nonneg _
  have hm : 0 ≤ m := hs.trans hsm
  set X : ℝ := M₀ ^ (q - 1) * (2 ^ q * (Ms + Mm)) with hX
  have hX0 : 0 ≤ X := by positivity
  refine ⟨X ^ ((1 : ℝ) / q), by positivity, ?_⟩
  intro C₀ hC₀ Ω _ P _ F x hF hB t ht ht1
  have hk : Measurable (fun y : ParabolicSpace => parabolicSemigroup.kernel t x y) :=
    measurable_parabolicSemigroup_kernel t x
  have hki : Integrable (fun y : ParabolicSpace => parabolicSemigroup.kernel t x y) := by
    have := parabolicSemigroup.integrable_moment ht (le_refl (0 : ℝ)) x
    refine (integrable_norm_iff hk.aestronglyMeasurable).1 ?_
    simpa using this
  have hd0 : ∀ y, 0 ≤ parabolicSemigroup.scaleDist y x := fun y =>
    parabolicSemigroup.scaleDist_nonneg y x
  have hB0 : ∀ y, 0 ≤ C₀ * (parabolicSemigroup.scaleDist y x ^ s +
      parabolicSemigroup.scaleDist y x ^ m) := fun y =>
    mul_nonneg hC₀ (add_nonneg (Real.rpow_nonneg (hd0 y) _) (Real.rpow_nonneg (hd0 y) _))
  have hpow : ∀ y, (C₀ * (parabolicSemigroup.scaleDist y x ^ s +
      parabolicSemigroup.scaleDist y x ^ m)) ^ q ≤
      C₀ ^ q * 2 ^ q * (parabolicSemigroup.scaleDist y x ^ (s * q) +
        parabolicSemigroup.scaleDist y x ^ (m * q)) := by
    intro y
    have h1 := add_pow_le_two_pow_mul (Real.rpow_nonneg (hd0 y) s) (Real.rpow_nonneg (hd0 y) m) q
    have e1 : (parabolicSemigroup.scaleDist y x ^ s) ^ q =
        parabolicSemigroup.scaleDist y x ^ (s * q) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hd0 y)]
    have e2 : (parabolicSemigroup.scaleDist y x ^ m) ^ q =
        parabolicSemigroup.scaleDist y x ^ (m * q) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hd0 y)]
    rw [e1, e2] at h1
    rw [mul_pow]
    calc C₀ ^ q * (parabolicSemigroup.scaleDist y x ^ s + parabolicSemigroup.scaleDist y x ^ m) ^ q
        ≤ C₀ ^ q * (2 ^ q * (parabolicSemigroup.scaleDist y x ^ (s * q) +
          parabolicSemigroup.scaleDist y x ^ (m * q))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by ring
  have hdm : Measurable (fun y : ParabolicSpace => parabolicSemigroup.scaleDist y x) :=
    (continuous_parabolicNorm.comp (continuous_id.sub continuous_const)).measurable
  have hdom : Integrable (fun y => C₀ ^ q * 2 ^ q * (|parabolicSemigroup.kernel t x y| *
      parabolicSemigroup.scaleDist y x ^ (s * q) + |parabolicSemigroup.kernel t x y| *
      parabolicSemigroup.scaleDist y x ^ (m * q))) := by
    refine Integrable.const_mul ?_ _
    exact (parabolicSemigroup.integrable_moment ht (r := s * q) (by positivity) x).add
      (parabolicSemigroup.integrable_moment ht (r := m * q) (by positivity) x)
  have hint : Integrable (fun y => |parabolicSemigroup.kernel t x y| *
      (C₀ * (parabolicSemigroup.scaleDist y x ^ s + parabolicSemigroup.scaleDist y x ^ m)) ^ q) := by
    refine hdom.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
    · exact ((continuous_abs.measurable.comp hk).mul (((measurable_const.mul ((hdm.pow_const s).add (hdm.pow_const m)))).pow_const
        q)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg (hB0 y) _))]
      calc _ ≤ |parabolicSemigroup.kernel t x y| * (C₀ ^ q * 2 ^ q *
            (parabolicSemigroup.scaleDist y x ^ (s * q) +
              parabolicSemigroup.scaleDist y x ^ (m * q))) :=
            mul_le_mul_of_nonneg_left (hpow y) (abs_nonneg _)
        _ = _ := by ring
  have h1 : ∫ y, |parabolicSemigroup.kernel t x y| ≤ M₀ := by
    have := parabolicSemigroup.moment_le ht (le_refl (0 : ℝ)) x
    simpa [hM₀] using this
  have hq4 : parabolicSemigroup.order = 4 := rfl
  have hms : ∫ y, |parabolicSemigroup.kernel t x y| * parabolicSemigroup.scaleDist y x ^ (s * q) ≤
      Ms * t ^ (s * q / 4) := by
    have := parabolicSemigroup.moment_le ht (r := s * q) (by positivity) x
    rwa [hq4] at this
  have hmm : ∫ y, |parabolicSemigroup.kernel t x y| * parabolicSemigroup.scaleDist y x ^ (m * q) ≤
      Mm * t ^ (m * q / 4) := by
    have := parabolicSemigroup.moment_le ht (r := m * q) (by positivity) x
    rwa [hq4] at this
  have htm : t ^ (m * q / 4) ≤ t ^ (s * q / 4) := by
    refine Real.rpow_le_rpow_of_exponent_ge ht ht1 ?_
    have := mul_le_mul_of_nonneg_right hsm (Nat.cast_nonneg (α := ℝ) q)
    linarith
  have h2 : ∫ y, |parabolicSemigroup.kernel t x y| * (C₀ * (parabolicSemigroup.scaleDist y x ^ s +
      parabolicSemigroup.scaleDist y x ^ m)) ^ q ≤ C₀ ^ q * 2 ^ q * ((Ms + Mm) * t ^ (s * q / 4)) := by
    calc _ ≤ ∫ y, C₀ ^ q * 2 ^ q * (|parabolicSemigroup.kernel t x y| *
          parabolicSemigroup.scaleDist y x ^ (s * q) + |parabolicSemigroup.kernel t x y| *
          parabolicSemigroup.scaleDist y x ^ (m * q)) := by
          refine integral_mono hint hdom fun y => ?_
          calc _ ≤ |parabolicSemigroup.kernel t x y| * (C₀ ^ q * 2 ^ q *
              (parabolicSemigroup.scaleDist y x ^ (s * q) +
                parabolicSemigroup.scaleDist y x ^ (m * q))) :=
                mul_le_mul_of_nonneg_left (hpow y) (abs_nonneg _)
            _ = _ := by ring
      _ = C₀ ^ q * 2 ^ q * ((∫ y, |parabolicSemigroup.kernel t x y| *
            parabolicSemigroup.scaleDist y x ^ (s * q)) + ∫ y, |parabolicSemigroup.kernel t x y| *
            parabolicSemigroup.scaleDist y x ^ (m * q)) := by
          rw [integral_const_mul, integral_add
            (parabolicSemigroup.integrable_moment ht (r := s * q) (by positivity) x)
            (parabolicSemigroup.integrable_moment ht (r := m * q) (by positivity) x)]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          nlinarith [mul_le_mul_of_nonneg_left htm hMm0, hms, hmm]
  have key := lintegral_enorm_integral_mul_pow_le_of_bound (P := P) hk hki hF hq hB0 hB h1 hint h2
  refine key.trans (le_of_eq ?_)
  have htq : (t ^ (s / 4)) ^ q = t ^ (s * q / 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    congr 1
    ring
  have hXq : (X ^ ((1 : ℝ) / q)) ^ q = X := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX0, one_div, inv_mul_cancel₀ (by positivity),
      Real.rpow_one]
  rw [← ENNReal.ofReal_pow (by positivity), mul_pow, mul_pow, hXq, htq]
  congr 1
  rw [hX]
  ring

end RegularityStructures.Phi43

end
