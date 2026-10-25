/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.Operator
public import RegularityStructures.Analysis.Semigroup.OperatorBound
public import RegularityStructures.Analysis.Semigroup.PairingGrowth.Moment
public import RegularityStructures.Analysis.Semigroup.Pairing.Limit

/-!
# Kernel tails of a regularising semigroup

Markov's inequality applied to the moment bounds `∫ |Q_t(x, y)| d(y, x)^r ≤ M_r t^{r/ℓ}`:

* `integral_abs_kernel_mul_div_pow_le`: `∫ |Q_t(x, y)| (d(y, x)/r)^k ≤ M_k t^{k/ℓ} r^{-k}`
  (no measurability needed; this is the form used in the locality estimates);
* `integral_tail_abs_kernel_le`: `∫_{d(y, x) ≥ r} |Q_t(x, y)| ≤ M_k t^{k/ℓ} r^{-k}`;
* weighted versions with `(1 + d(y, x))^q`, `q ≥ 0`, for `0 < t ≤ 1`:
  `∫_{d(y, x) ≥ r} |Q_t(x, y)| (1 + d(y, x))^q ≤ 2^q (M_k + M_{q+k}) t^{k/ℓ} r^{-k}`.

The set versions assume the tail set is measurable (the interface does not make `scaleDist`
measurable).
-/

public section

open MeasureTheory Set

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)

theorem abs_kernel_mul_div_pow_eq (t : ℝ) (x y : E) {k r : ℝ} (hr : 0 < r) :
    |K.kernel t x y| * (K.scaleDist y x / r) ^ k =
      (|K.kernel t x y| * K.scaleDist y x ^ k) * r ^ (-k) := by
  rw [Real.div_rpow (K.scaleDist_nonneg _ _) hr.le, Real.rpow_neg hr.le, div_eq_mul_inv]
  ring

theorem integrable_abs_kernel_mul_div_pow {t : ℝ} (ht : 0 < t) {k r : ℝ} (hk : 0 ≤ k)
    (hr : 0 < r) (x : E) :
    Integrable (fun y => |K.kernel t x y| * (K.scaleDist y x / r) ^ k) μ := by
  simp_rw [K.abs_kernel_mul_div_pow_eq t x _ hr]
  exact (K.integrable_moment ht hk x).mul_const _

/-- Markov for the kernel, in function form: `∫ |Q_t(x, y)| (d(y, x)/r)^k ≤ M_k t^{k/ℓ} r^{-k}`. -/
theorem integral_abs_kernel_mul_div_pow_le {t : ℝ} (ht : 0 < t) {k r : ℝ} (hk : 0 ≤ k)
    (hr : 0 < r) (x : E) :
    ∫ y, |K.kernel t x y| * (K.scaleDist y x / r) ^ k ∂μ ≤
      K.momentConst k * t ^ (k / K.order) * r ^ (-k) := by
  simp_rw [K.abs_kernel_mul_div_pow_eq t x _ hr]
  rw [integral_mul_const]
  exact mul_le_mul_of_nonneg_right (K.moment_le ht hk x) (Real.rpow_nonneg hr.le _)

/-- **Kernel tail**: `∫_{d(y, x) ≥ r} |Q_t(x, y)| dμ(y) ≤ M_k t^{k/ℓ} r^{-k}`. -/
theorem integral_tail_abs_kernel_le {t : ℝ} (ht : 0 < t) {k r : ℝ} (hk : 0 ≤ k) (hr : 0 < r)
    (x : E) (hS : MeasurableSet {y | r ≤ K.scaleDist y x}) :
    ∫ y in {y | r ≤ K.scaleDist y x}, |K.kernel t x y| ∂μ ≤
      K.momentConst k * t ^ (k / K.order) * r ^ (-k) := by
  have hi := K.integrable_abs_kernel_mul_div_pow ht hk hr x
  calc ∫ y in {y | r ≤ K.scaleDist y x}, |K.kernel t x y| ∂μ
      ≤ ∫ y in {y | r ≤ K.scaleDist y x}, |K.kernel t x y| * (K.scaleDist y x / r) ^ k ∂μ := by
        refine setIntegral_mono_on (K.integrable_kernel ht x).abs.integrableOn hi.integrableOn hS
          fun y hy => ?_
        have h1 : 1 ≤ (K.scaleDist y x / r) ^ k :=
          Real.one_le_rpow ((one_le_div hr).2 hy) hk
        exact le_mul_of_one_le_right (abs_nonneg _) h1
    _ ≤ ∫ y, |K.kernel t x y| * (K.scaleDist y x / r) ^ k ∂μ :=
        setIntegral_le_integral hi (Filter.Eventually.of_forall fun y =>
          mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (div_nonneg (K.scaleDist_nonneg _ _) hr.le) _))
    _ ≤ _ := K.integral_abs_kernel_mul_div_pow_le ht hk hr x

private theorem one_add_rpow_le {d q : ℝ} (hd : 0 ≤ d) (hq : 0 ≤ q) :
    (1 + d) ^ q ≤ 2 ^ q * (1 + d ^ q) := by
  have h := rpow_mul_rpow_le (D := d) (w := d) (b := 1) (q := q) (r := 0) hd hd le_rfl hq
    le_rfl (by linarith)
  simp only [Real.rpow_zero, mul_one, add_zero, Real.one_rpow] at h
  linarith

end RegularityStructures.RegularisingSemigroup

end

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)

/-- The dominating function for the weighted tail estimates. -/
def weightMajorant (t : ℝ) (x : E) (q k r : ℝ) (y : E) : ℝ :=
  2 ^ q * (|K.kernel t x y| * (K.scaleDist y x / r) ^ k +
    (|K.kernel t x y| * K.scaleDist y x ^ (q + k)) * r ^ (-k))

end RegularityStructures.RegularisingSemigroup

end

public section

open MeasureTheory Set

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)

theorem abs_kernel_mul_weight_le_majorant (t : ℝ) {q k r : ℝ} (hq : 0 ≤ q) (hk : 0 ≤ k)
    (hr : 0 < r) (x y : E) :
    |K.kernel t x y| * ((1 + K.scaleDist y x) ^ q * (K.scaleDist y x / r) ^ k) ≤
      K.weightMajorant t x q k r y := by
  have hd := K.scaleDist_nonneg y x
  have hw := one_add_rpow_le hd hq
  have hs : K.scaleDist y x ^ q * (K.scaleDist y x / r) ^ k =
      K.scaleDist y x ^ (q + k) * r ^ (-k) := by
    rw [Real.rpow_add_of_nonneg hd hq hk, Real.div_rpow hd hr.le, Real.rpow_neg hr.le,
      div_eq_mul_inv]
    ring
  have hQ := abs_nonneg (K.kernel t x y)
  have hk0 : 0 ≤ (K.scaleDist y x / r) ^ k := Real.rpow_nonneg (div_nonneg hd hr.le) _
  calc |K.kernel t x y| * ((1 + K.scaleDist y x) ^ q * (K.scaleDist y x / r) ^ k)
      ≤ |K.kernel t x y| * (2 ^ q * (1 + K.scaleDist y x ^ q) *
          (K.scaleDist y x / r) ^ k) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hw hk0) hQ
    _ = 2 ^ q * (|K.kernel t x y| * (K.scaleDist y x / r) ^ k +
          |K.kernel t x y| * (K.scaleDist y x ^ q * (K.scaleDist y x / r) ^ k)) := by ring
    _ = _ := by rw [hs, weightMajorant]; ring

theorem integrable_weightMajorant {t : ℝ} (ht : 0 < t) {q k r : ℝ} (hq : 0 ≤ q) (hk : 0 ≤ k)
    (hr : 0 < r) (x : E) : Integrable (K.weightMajorant t x q k r) μ :=
  ((K.integrable_abs_kernel_mul_div_pow ht hk hr x).add
    ((K.integrable_moment ht (add_nonneg hq hk) x).mul_const _)).const_mul _

theorem integral_weightMajorant_le {t : ℝ} (ht : 0 < t) {q k r : ℝ} (hq : 0 ≤ q) (hk : 0 ≤ k)
    (hr : 0 < r) (x : E) :
    ∫ y, K.weightMajorant t x q k r y ∂μ ≤
      2 ^ q * ((K.momentConst k * t ^ (k / K.order) +
        K.momentConst (q + k) * t ^ ((q + k) / K.order)) * r ^ (-k)) := by
  have hqk : 0 ≤ q + k := add_nonneg hq hk
  have hi1 := K.integrable_abs_kernel_mul_div_pow ht hk hr x
  have hi2 : Integrable (fun y => (|K.kernel t x y| * K.scaleDist y x ^ (q + k)) * r ^ (-k)) μ :=
    (K.integrable_moment ht hqk x).mul_const _
  unfold weightMajorant
  rw [integral_const_mul, integral_add hi1 hi2, integral_mul_const]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by norm_num) _)
  have a1 := K.integral_abs_kernel_mul_div_pow_le ht hk hr x
  have a2 := mul_le_mul_of_nonneg_right (K.moment_le ht hqk x) (Real.rpow_nonneg hr.le (-k))
  linarith

/-- Weighted kernel tail for `0 < t ≤ 1`, `q, k ≥ 0`:
`∫_{d(y, x) ≥ r} |Q_t(x, y)| (1 + d(y, x))^q ≤ 2^q (M_k + M_{q+k}) t^{k/ℓ} r^{-k}`. -/
theorem integral_tail_abs_kernel_mul_weight_le {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) {q k r : ℝ}
    (hq : 0 ≤ q) (hk : 0 ≤ k) (hr : 0 < r) (x : E)
    (hS : MeasurableSet {y | r ≤ K.scaleDist y x}) :
    ∫ y in {y | r ≤ K.scaleDist y x}, |K.kernel t x y| * (1 + K.scaleDist y x) ^ q ∂μ ≤
      2 ^ q * (K.momentConst k + K.momentConst (q + k)) * t ^ (k / K.order) * r ^ (-k) := by
  have hqk : 0 ≤ q + k := add_nonneg hq hk
  have hint := K.integrable_weightMajorant ht.1 hq hk hr x
  have hmaj : 0 ≤ᵐ[μ] K.weightMajorant t x q k r := Filter.Eventually.of_forall fun y =>
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (add_nonneg
      (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (div_nonneg (K.scaleDist_nonneg _ _) hr.le) _))
      (mul_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (K.scaleDist_nonneg _ _) _))
        (Real.rpow_nonneg hr.le _)))
  have h1 : ∫ y in {y | r ≤ K.scaleDist y x}, |K.kernel t x y| * (1 + K.scaleDist y x) ^ q ∂μ ≤
      ∫ y in {y | r ≤ K.scaleDist y x}, K.weightMajorant t x q k r y ∂μ := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y =>
      mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (by linarith [K.scaleDist_nonneg y x]) _))
      hint.integrableOn ((ae_restrict_iff' hS).2 (Filter.Eventually.of_forall fun y hy => ?_))
    have h1 : 1 ≤ (K.scaleDist y x / r) ^ k := Real.one_le_rpow ((one_le_div hr).2 hy) hk
    refine le_trans ?_ (K.abs_kernel_mul_weight_le_majorant t hq hk hr x y)
    calc |K.kernel t x y| * (1 + K.scaleDist y x) ^ q
        = |K.kernel t x y| * ((1 + K.scaleDist y x) ^ q * 1) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1
          (Real.rpow_nonneg (by linarith [K.scaleDist_nonneg y x]) _)) (abs_nonneg _)
  refine h1.trans ((setIntegral_le_integral hint hmaj).trans
    ((K.integral_weightMajorant_le ht.1 hq hk hr x).trans ?_))
  have h3 : t ^ ((q + k) / K.order) ≤ t ^ (k / K.order) :=
    Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2
      (div_le_div_of_nonneg_right (by linarith) K.order_pos.le)
  have hM := K.momentConst_nonneg (q + k)
  have hr0 := Real.rpow_nonneg hr.le (-k)
  have h2q := Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) q
  have : K.momentConst (q + k) * t ^ ((q + k) / K.order) ≤
      K.momentConst (q + k) * t ^ (k / K.order) := mul_le_mul_of_nonneg_left h3 hM
  calc 2 ^ q * ((K.momentConst k * t ^ (k / K.order) +
        K.momentConst (q + k) * t ^ ((q + k) / K.order)) * r ^ (-k))
      ≤ 2 ^ q * ((K.momentConst k * t ^ (k / K.order) +
        K.momentConst (q + k) * t ^ (k / K.order)) * r ^ (-k)) := by gcongr
    _ = _ := by ring

end RegularityStructures.RegularisingSemigroup

end
