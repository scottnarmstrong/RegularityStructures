/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import GlobalPhi43.MW20.Setting.IsMWTestKernel
public import GlobalPhi43.MW20.Setting.MWKernel
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Characterisation theorems for the definitions of the MW20 setting

This file holds the characterisation theorems paired with the definitions of the MW20 setting in
`GlobalPhi43.MW20.Setting`: theorems showing that a definition means what its docstring says.

* `GlobalPhi43.tendsto_mwKernelSeq_mwKernel`: for an admissible test kernel `Φ` and `T > 0`, the iterated
  kernels `mwKernelSeq Φ T n` converge pointwise, so `mwKernel Φ T` is their genuine pointwise limit.

The proof: each rescaling `parabolicRescale Φ S` (`S > 0`) is nonnegative, continuous, of mass one and supported
in the ball of radius `max (S ^ 2) S`; convolution with it preserves a Lipschitz constant `L` and moves a function
by at most `L * max (S ^ 2) S` in sup norm. With `S = T / 2 ^ (n + 2)` the increments are geometric.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff NNReal

namespace GlobalPhi43

open RegularityStructures

namespace MWKernelChar

variable {Φ : ParabolicSpace → ℝ}

lemma pastBall_zero_one_bound {w : ParabolicSpace} (hw : w ∈ pastBall 0 1) :
    |w.1| < 1 ∧ ‖w.2‖ < 1 := by
  simp only [pastBall, parabolicDist, mem_ofPred_eq, max_lt_iff, zero_sub, abs_neg, norm_neg,
    Prod.fst_zero, Prod.snd_zero] at hw
  refine ⟨?_, hw.1.2⟩
  have := (Real.sqrt_lt' one_pos).1 hw.1.1
  simpa using this

lemma norm_lt_of_pastBall {w : ParabolicSpace} (hw : w ∈ pastBall 0 1) : ‖w‖ < 1 := by
  obtain ⟨h1, h2⟩ := pastBall_zero_one_bound hw
  rw [Prod.norm_def]
  exact max_lt (by simpa [Real.norm_eq_abs] using h1) h2

lemma hasCompactSupport (hΦ : IsMWTestKernel Φ) : HasCompactSupport Φ :=
  (isCompact_closedBall (0 : ParabolicSpace) 1).of_isClosed_subset (isClosed_tsupport _)
    fun _w hw => mem_closedBall_zero_iff.2 (norm_lt_of_pastBall (hΦ.2.1 hw)).le

lemma rescale_norm_lt (hΦ : IsMWTestKernel Φ) {S : ℝ} (hS : 0 < S) {u : ParabolicSpace}
    (hu : parabolicRescale Φ S u ≠ 0) : ‖u‖ < max (S ^ 2) S := by
  have h1 : Φ (u.1 / S ^ 2, S⁻¹ • u.2) ≠ 0 := right_ne_zero_of_mul hu
  obtain ⟨a, b⟩ := pastBall_zero_one_bound (hΦ.2.1 (subset_tsupport _ h1))
  have hS2 : 0 < S ^ 2 := pow_pos hS 2
  simp only at a b
  rw [abs_div, abs_of_pos hS2, div_lt_one hS2] at a
  rw [norm_smul, norm_inv, Real.norm_of_nonneg hS.le, inv_mul_lt_iff₀ hS, mul_one] at b
  rw [Prod.norm_def]
  exact max_lt (lt_max_of_lt_left (by simpa [Real.norm_eq_abs] using a)) (lt_max_of_lt_right b)

lemma rescale_nonneg (hΦ : IsMWTestKernel Φ) {S : ℝ} (hS : 0 < S) (u : ParabolicSpace) :
    0 ≤ parabolicRescale Φ S u :=
  mul_nonneg (zpow_nonneg hS.le _) (hΦ.2.2.1 _).1

lemma rescale_contDiff (hΦ : IsMWTestKernel Φ) (S : ℝ) : ContDiff ℝ ∞ (parabolicRescale Φ S) :=
  ContDiff.mul contDiff_const (hΦ.1.comp ((contDiff_fst.div_const _).prodMk (contDiff_snd.const_smul _)))

lemma rescale_continuous (hΦ : IsMWTestKernel Φ) (S : ℝ) : Continuous (parabolicRescale Φ S) :=
  (rescale_contDiff hΦ S).continuous

lemma rescale_hasCompactSupport (hΦ : IsMWTestKernel Φ) {S : ℝ} (hS : 0 < S) :
    HasCompactSupport (parabolicRescale Φ S) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ParabolicSpace) (max (S ^ 2) S)) fun _u hu =>
    by_contra fun h => hu (mem_closedBall_zero_iff.2 (rescale_norm_lt hΦ hS h).le)

lemma integral_rescale (hΦ : IsMWTestKernel Φ) {S : ℝ} (hS : 0 < S) :
    ∫ z, parabolicRescale Φ S z = 1 := by
  have hint : Integrable Φ (volume.prod volume) :=
    hΦ.1.continuous.integrable_of_hasCompactSupport (hasCompactSupport hΦ)
  have hintS : Integrable (parabolicRescale Φ S) (volume.prod volume) :=
    (rescale_continuous hΦ S).integrable_of_hasCompactSupport (rescale_hasCompactSupport hΦ hS)
  have hmass : ∫ z, Φ z ∂(volume.prod volume) = 1 := hΦ.2.2.2.1
  rw [Measure.volume_eq_prod, integral_prod _ hintS]
  have inner : ∀ t : ℝ, ∫ x : Fin 3 → ℝ, parabolicRescale Φ S (t, x) =
      S ^ (-5 : ℤ) * S ^ 3 * ∫ x : Fin 3 → ℝ, Φ (t / S ^ 2, x) := by
    intro t
    simp only [parabolicRescale]
    rw [integral_const_mul,
      Measure.integral_comp_inv_smul_of_nonneg volume (fun x => Φ (t / S ^ 2, x)) hS.le]
    simp [mul_assoc]
  simp_rw [inner]
  rw [integral_const_mul]
  have outer : ∫ t : ℝ, ∫ x : Fin 3 → ℝ, Φ (t / S ^ 2, x) =
      S ^ 2 * ∫ t : ℝ, ∫ x : Fin 3 → ℝ, Φ (t, x) := by
    have := Measure.integral_comp_inv_smul_of_nonneg volume
      (fun t : ℝ => ∫ x : Fin 3 → ℝ, Φ (t, x)) (sq_nonneg S)
    simpa [div_eq_inv_mul] using this
  rw [outer, ← integral_prod _ hint, hmass, mul_one]
  have hS0 : S ≠ 0 := hS.ne'
  have h5 : S ^ 3 * S ^ 2 = S ^ 5 := by ring
  rw [zpow_neg, zpow_ofNat, mul_assoc, h5, inv_mul_cancel₀ (pow_ne_zero 5 hS0)]

lemma integrable_mul_rescale (hΦ : IsMWTestKernel Φ) {S : ℝ} (hS : 0 < S) {f : ParabolicSpace → ℝ}
    (hf : Continuous f) (z : ParabolicSpace) :
    Integrable (fun u => f (z - u) * parabolicRescale Φ S u) := by
  have hc : Continuous (fun u => f (z - u) * parabolicRescale Φ S u) :=
    (hf.comp (continuous_const.sub continuous_id)).mul (rescale_continuous hΦ S)
  exact hc.integrable_of_hasCompactSupport (μ := volume) (rescale_hasCompactSupport hΦ hS).mul_left

lemma conv_eq (f : ParabolicSpace → ℝ) (S : ℝ) (z : ParabolicSpace) :
    MeasureTheory.convolution f (parabolicRescale Φ S) (ContinuousLinearMap.lsmul ℝ ℝ) volume z =
      ∫ u, f (z - u) * parabolicRescale Φ S u := by
  have : (volume : Measure ParabolicSpace).IsAddLeftInvariant := by
    rw [Measure.volume_eq_prod]; infer_instance
  have : (volume : Measure ParabolicSpace).IsNegInvariant := by
    rw [Measure.volume_eq_prod]; exact Measure.IsAddHaarMeasure.isNegInvariant_of_regular _
  rw [convolution_lsmul_swap]
  simp only [smul_eq_mul]

lemma conv_lipschitz (hΦ : IsMWTestKernel Φ) {S : ℝ} (hS : 0 < S) {L : ℝ≥0}
    {f : ParabolicSpace → ℝ} (hf : LipschitzWith L f) :
    LipschitzWith L
      (MeasureTheory.convolution f (parabolicRescale Φ S) (ContinuousLinearMap.lsmul ℝ ℝ) volume) := by
  refine LipschitzWith.of_dist_le_mul fun z z' => ?_
  rw [conv_eq, conv_eq, Real.dist_eq,
    ← integral_sub (integrable_mul_rescale hΦ hS hf.continuous z)
      (integrable_mul_rescale hΦ hS hf.continuous z')]
  calc |∫ u, (f (z - u) * parabolicRescale Φ S u - f (z' - u) * parabolicRescale Φ S u)|
      ≤ ∫ u, (L : ℝ) * dist z z' * parabolicRescale Φ S u := by
        rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le
          (((rescale_continuous hΦ S).integrable_of_hasCompactSupport (μ := volume)
            (rescale_hasCompactSupport hΦ hS)).const_mul ((L : ℝ) * dist z z')) (Eventually.of_forall fun u => ?_)
        rw [← sub_mul, norm_mul, Real.norm_of_nonneg (rescale_nonneg hΦ hS u)]
        refine mul_le_mul_of_nonneg_right ?_ (rescale_nonneg hΦ hS u)
        have := hf.dist_le_mul (z - u) (z' - u)
        rwa [dist_sub_right, Real.dist_eq] at this
    _ = (L : ℝ) * dist z z' := by rw [integral_const_mul, integral_rescale hΦ hS, mul_one]

lemma conv_dist_le (hΦ : IsMWTestKernel Φ) {S : ℝ} (hS : 0 < S) {L : ℝ≥0}
    {f : ParabolicSpace → ℝ} (hf : LipschitzWith L f) (z : ParabolicSpace) :
    dist (MeasureTheory.convolution f (parabolicRescale Φ S) (ContinuousLinearMap.lsmul ℝ ℝ) volume z)
      (f z) ≤ L * max (S ^ 2) S := by
  have hψ : Integrable (parabolicRescale Φ S) :=
    (rescale_continuous hΦ S).integrable_of_hasCompactSupport (rescale_hasCompactSupport hΦ hS)
  rw [conv_eq, Real.dist_eq]
  calc |(∫ u, f (z - u) * parabolicRescale Φ S u) - f z|
      = |∫ u, (f (z - u) * parabolicRescale Φ S u - f z * parabolicRescale Φ S u)| := by
        rw [integral_sub (integrable_mul_rescale hΦ hS hf.continuous z) (hψ.const_mul (f z)),
          integral_const_mul, integral_rescale hΦ hS, mul_one]
    _ ≤ ∫ u, (L : ℝ) * max (S ^ 2) S * parabolicRescale Φ S u := by
        rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le (hψ.const_mul ((L : ℝ) * max (S ^ 2) S)) (Eventually.of_forall fun u => ?_)
        rw [← sub_mul, norm_mul, Real.norm_of_nonneg (rescale_nonneg hΦ hS u)]
        by_cases h0 : parabolicRescale Φ S u = 0
        · simp [h0]
        refine mul_le_mul_of_nonneg_right ?_ (rescale_nonneg hΦ hS u)
        have h1 := hf.dist_le_mul (z - u) z
        have h2 : dist (z - u) z = ‖u‖ := by rw [dist_eq_norm]; simp
        rw [h2, Real.dist_eq] at h1
        exact h1.trans (mul_le_mul_of_nonneg_left (rescale_norm_lt hΦ hS h0).le L.2)
    _ = (L : ℝ) * max (S ^ 2) S := by rw [integral_const_mul, integral_rescale hΦ hS, mul_one]

lemma exists_lipschitz (hΦ : IsMWTestKernel Φ) {T : ℝ} (hT : 0 < T) :
    ∃ L : ℝ≥0, ∀ n, LipschitzWith L (mwKernelSeq Φ T n) := by
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (rescale_hasCompactSupport hΦ (half_pos hT)) (rescale_contDiff hΦ (T / 2)) (by simp)
  refine ⟨L, fun n => ?_⟩
  induction n with
  | zero => exact hL
  | succ n ih => exact conv_lipschitz hΦ (by positivity) ih

lemma scale_bound {T : ℝ} (hT : 0 < T) (n : ℕ) :
    max ((T / 2 ^ (n + 2)) ^ 2) (T / 2 ^ (n + 2)) ≤ (T ^ 2 + T) * (1 / 2) ^ n := by
  set q : ℝ := (1 / 2) ^ n with hq
  have hq0 : 0 < q := by positivity
  have hq1 : q ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hS : T / 2 ^ (n + 2) = T * q / 4 := by
    rw [hq, pow_add, one_div_pow]; field_simp; norm_num
  rw [hS]
  have h1 : T * q / 4 ≤ T * q := by nlinarith
  have h2 : (T * q / 4) ^ 2 ≤ T ^ 2 * q := by
    have : (T * q / 4) ^ 2 = T ^ 2 * q * (q / 16) := by ring
    rw [this]
    exact mul_le_of_le_one_right (by positivity) (by linarith)
  refine max_le ?_ ?_ <;> nlinarith [sq_nonneg T]

end MWKernelChar

open MWKernelChar in
/-- For an admissible MW20 test kernel `Φ` and `T > 0`, the finite iterated kernels `mwKernelSeq Φ T n`
converge pointwise to `mwKernel Φ T`: the `limUnder` in the definition of `mwKernel` is a genuine limit. -/
theorem tendsto_mwKernelSeq_mwKernel {Φ : ParabolicSpace → ℝ} (hΦ : IsMWTestKernel Φ) {T : ℝ} (hT : 0 < T)
    (z : ParabolicSpace) :
    Filter.Tendsto (fun n => mwKernelSeq Φ T n z) Filter.atTop (nhds (mwKernel Φ T z)) := by
  obtain ⟨L, hL⟩ := exists_lipschitz hΦ hT
  have hc : CauchySeq (fun n => mwKernelSeq Φ T n z) := by
    refine cauchySeq_of_le_geometric (1 / 2) (L * (T ^ 2 + T)) (by norm_num) fun n => ?_
    rw [dist_comm]
    have hS : 0 < T / 2 ^ (n + 2) := by positivity
    calc dist (mwKernelSeq Φ T (n + 1) z) (mwKernelSeq Φ T n z)
        ≤ L * max ((T / 2 ^ (n + 2)) ^ 2) (T / 2 ^ (n + 2)) := conv_dist_le hΦ hS (hL n) z
      _ ≤ L * ((T ^ 2 + T) * (1 / 2) ^ n) := mul_le_mul_of_nonneg_left (scale_bound hT n) L.2
      _ = L * (T ^ 2 + T) * (1 / 2) ^ n := by ring
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hc
  exact tendsto_nhds_limUnder ⟨a, ha⟩

end GlobalPhi43

end
