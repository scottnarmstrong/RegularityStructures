module

public import GlobalPhi43.MW20.InfiniteKernelMeasure
public import Mathlib.Algebra.Order.Ring.Abs

/-!
# The analytic cubic commutator in MW20 (4.30)
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory

/-- The cubic map has Lipschitz constant 3M² on [-M,M]. -/
theorem abs_cube_sub_cube_le {a b M : ℝ} (ha : |a| ≤ M) (hb : |b| ≤ M) :
    |a ^ 3 - b ^ 3| ≤ 3 * M ^ 2 * |a - b| := by
  have hM : 0 ≤ M := (abs_nonneg a).trans ha
  have h := abs_pow_sub_pow_le (a := a) (b := b) (n := 3)
  have hm : max |a| |b| ≤ M := max_le ha hb
  have hpow : max |a| |b| ^ 2 ≤ M ^ 2 :=
    pow_le_pow_left₀ (le_trans (abs_nonneg a) (le_max_left _ _)) hm 2
  norm_num only [Nat.cast_ofNat, Nat.reduceSub] at h
  nlinarith [mul_le_mul_of_nonneg_left hpow (mul_nonneg (abs_nonneg (a - b)) (by norm_num : (0 : ℝ) ≤ 3))]

/-- The actual probability average cubic commutator, from local amplitude
and oscillation bounds. Neither commutation nor its bound is a premise. -/
theorem probability_cubic_commutator {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (f : E → ℝ)
    (hf : AEStronglyMeasurable f μ) {M δ b : ℝ}
    (hbound : ∀ᵐ y ∂μ, |f y| ≤ M) (hosc : ∀ᵐ y ∂μ, |f y - b| ≤ δ) :
    |(∫ y, f y ∂μ) ^ 3 - ∫ y, (f y) ^ 3 ∂μ| ≤ 6 * M ^ 2 * δ := by
  have hi : Integrable f μ := (integrable_const M).mono' hf (by simpa only [Real.norm_eq_abs] using hbound)
  have hcube : Integrable (fun y => (f y) ^ 3) μ := by
    apply (integrable_const (M ^ 3)).mono' (hf.pow 3)
    filter_upwards [hbound] with y hy
    simpa only [Real.norm_eq_abs, abs_pow, Pi.pow_apply] using pow_le_pow_left₀ (abs_nonneg _) hy 3
  let a := ∫ y, f y ∂μ
  have hbn : ∀ᵐ y ∂μ, ‖f y‖ ≤ M := by simpa only [Real.norm_eq_abs] using hbound
  have ha : |a| ≤ M := by
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using norm_integral_le_of_norm_le_const hbn
  have hab : |a - b| ≤ δ := by
    have he : a - b = ∫ y, f y - b ∂μ := by
      rw [integral_sub hi (integrable_const b)]
      simp [a]
    rw [he]
    have hon : ∀ᵐ y ∂μ, ‖f y - b‖ ≤ δ := by simpa only [Real.norm_eq_abs] using hosc
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using norm_integral_le_of_norm_le_const hon
  have he : a ^ 3 - (∫ y, (f y) ^ 3 ∂μ) = ∫ y, a ^ 3 - (f y) ^ 3 ∂μ := by
    rw [integral_sub (integrable_const _) hcube]
    simp
  change |a ^ 3 - (∫ y, (f y) ^ 3 ∂μ)| ≤ _
  rw [he]
  have hdiff : ∀ᵐ y ∂μ, ‖a ^ 3 - (f y) ^ 3‖ ≤ 6 * M ^ 2 * δ := by
    filter_upwards [hbound, hosc] with y hy hyosc
    rw [Real.norm_eq_abs]
    have hd : |a - f y| ≤ 2 * δ := by
      calc
        _ = |(a - b) - (f y - b)| := by congr 1; ring
        _ ≤ |a - b| + |f y - b| := abs_sub _ _
        _ ≤ 2 * δ := by linarith
    exact (abs_cube_sub_cube_le ha hy).trans (by nlinarith [sq_nonneg M])
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using norm_integral_le_of_norm_le_const hdiff


end GlobalPhi43.MW20
