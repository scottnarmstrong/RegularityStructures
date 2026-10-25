/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.PolyCompat.ApproxPoly
public import RegularityStructures.Abstract.Polynomial.Model.Growth
public import RegularityStructures.Analysis.Kernel.Moments

/-!
# The pairing of a polynomial with a test function

For a continuous `g` of polynomial growth and a continuous compactly supported test function `φ`,
`∫ Q_s g · φ → ∫ g · φ` as `s ↓ 0` (dominated convergence, the uniform bound being the moment bound
`kernelPowMoment_le`). Hence the pairing `⟨g, φ⟩` of `parabolicSemigroup` equals `∫ g φ`
(`pairing_eq_integral_of_polyBounded`); in particular for the polynomials `Π_y X^l = (· - y)^l`.
-/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace RegularityStructures

theorem integral_abs_parabolicKernel_mul_norm_le {t : ℝ} (ht : 0 < t) {r : ℝ} (hr : 0 ≤ r) :
    ∫ w, |parabolicKernel t w| * parabolicNorm w ^ r ≤ parabolicMomentConst r * t ^ (r / 4) := by
  calc ∫ w, |parabolicKernel t w| * parabolicNorm w ^ r
      ≤ ∫ w, parabolicMomentBound t r w :=
        integral_mono (integrable_abs_parabolicKernel_mul_norm ht hr)
          (integrable_parabolicMomentBound ht hr) (fun w => abs_parabolicKernel_mul_le t hr w)
    _ = _ := integral_parabolicMomentBound ht hr

/-- The kernel moments `∫ |q_s| (1 + ‖·‖)^n` are bounded uniformly for `s ∈ (0, 1]`. -/
theorem exists_kernelPowMoment_le (n : ℕ) :
    ∃ C : ℝ, ∀ s : ℝ, 0 < s → s ≤ 1 → kernelPowMoment n s ≤ C := by
  refine ⟨2 ^ n * (parabolicMomentConst 0 + parabolicMomentConst n), fun s hs hs1 => ?_⟩
  have h0 := integral_abs_parabolicKernel_mul_norm_le hs (le_refl (0 : ℝ))
  have hn := integral_abs_parabolicKernel_mul_norm_le hs (Nat.cast_nonneg n)
  have i0 := integrable_abs_parabolicKernel_mul_norm hs (le_refl (0 : ℝ))
  have i1 := integrable_abs_parabolicKernel_mul_norm hs (Nat.cast_nonneg n)
  have e0 : s ^ ((0 : ℝ) / 4) ≤ 1 := Real.rpow_le_one hs.le hs1 (by norm_num)
  have e1 : s ^ ((n : ℝ) / 4) ≤ 1 := Real.rpow_le_one hs.le hs1 (by positivity)
  have hM0 := parabolicMomentConst_nonneg 0
  have hMn := parabolicMomentConst_nonneg n
  unfold kernelPowMoment
  calc ∫ a, |parabolicKernel s a| * (1 + parabolicNorm a) ^ n
      ≤ ∫ a, 2 ^ n * (|parabolicKernel s a| * parabolicNorm a ^ (0 : ℝ) +
          |parabolicKernel s a| * parabolicNorm a ^ (n : ℝ)) := by
        refine integral_mono (integrable_abs_parabolicKernel_mul_pow hs n)
          ((i0.add i1).const_mul _) fun a => ?_
        rw [Real.rpow_zero, Real.rpow_natCast, mul_one]
        calc |parabolicKernel s a| * (1 + parabolicNorm a) ^ n
            ≤ |parabolicKernel s a| * (2 ^ n * (1 + parabolicNorm a ^ n)) :=
              mul_le_mul_of_nonneg_left (one_add_pow_le _ (parabolicNorm_nonneg a) n)
                (abs_nonneg _)
          _ = _ := by ring
    _ = 2 ^ n * ((∫ a, |parabolicKernel s a| * parabolicNorm a ^ (0 : ℝ)) +
          ∫ a, |parabolicKernel s a| * parabolicNorm a ^ (n : ℝ)) := by
        rw [integral_const_mul, integral_add i0 i1]
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have a0 : parabolicMomentConst 0 * s ^ ((0 : ℝ) / 4) ≤ parabolicMomentConst 0 :=
          mul_le_of_le_one_right hM0 e0
        have a1 : parabolicMomentConst n * s ^ ((n : ℝ) / 4) ≤ parabolicMomentConst n :=
          mul_le_of_le_one_right hMn e1
        exact add_le_add (h0.trans a0) (hn.trans a1)

theorem abs_apply_le_of_kernelPowMoment_le {g : ParabolicSpace → ℝ} (hgm : Measurable g) {B : ℝ} {n : ℕ}
    (hB : ∀ u, |g u| ≤ B * (1 + parabolicNorm u) ^ n) {C : ℝ}
    (hC : ∀ s : ℝ, 0 < s → s ≤ 1 → kernelPowMoment n s ≤ C) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (z : ParabolicSpace) :
    |parabolicSemigroup.apply s g z| ≤ B * (C * (1 + parabolicNorm z) ^ n) := by
  have hB0 := nonneg_of_bound hB
  calc |parabolicSemigroup.apply s g z|
      ≤ ∫ w, |parabolicKernel s (z - w) * g w| := abs_integral_le_integral_abs
    _ ≤ B * ((1 + parabolicNorm z) ^ n * kernelPowMoment n s) :=
        integral_abs_parabolicKernel_mul_le hgm hB hs z
    _ ≤ B * ((1 + parabolicNorm z) ^ n * C) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hC s hs hs1)
          (pow_nonneg (by linarith [parabolicNorm_nonneg z]) _)) hB0
    _ = _ := by ring

/-- `∫ Q_s g · φ → ∫ g φ` as `s ↓ 0`, for `g` continuous of polynomial growth and `φ` continuous
with compact support. -/
theorem tendsto_integral_apply_mul {g φ : ParabolicSpace → ℝ} (hg : Continuous g) {B : ℝ} {n : ℕ}
    (hB : ∀ u, |g u| ≤ B * (1 + parabolicNorm u) ^ n) (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) :
    Tendsto (fun s => ∫ z, parabolicSemigroup.apply s g z * φ z) (𝓝[>] 0)
      (𝓝 (∫ z, g z * φ z)) := by
  obtain ⟨C, hC⟩ := exists_kernelPowMoment_le n
  have hbm : Continuous fun z => B * (C * (1 + parabolicNorm z) ^ n) * |φ z| := by
    have := continuous_parabolicNorm
    fun_prop
  have hbc : HasCompactSupport fun z => B * (C * (1 + parabolicNorm z) ^ n) * |φ z| :=
    hφc.abs.mul_left
  refine tendsto_integral_filter_of_dominated_convergence
    (fun z => B * (C * (1 + parabolicNorm z) ^ n) * |φ z|) ?_ ?_
    (hbm.integrable_of_hasCompactSupport hbc) ?_
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact ((parabolicSemigroup.measurable_apply s hg.measurable).mul
      hφ.measurable).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with s hs
    refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right
      (abs_apply_le_of_kernelPowMoment_le hg.measurable hB hC hs.1 hs.2.le z) (abs_nonneg _)
  · refine Filter.Eventually.of_forall fun z => ?_
    exact (tendsto_apply_parabolicSemigroup_nhdsGT hg hB z).mul_const _

/-- The pairing `⟨Λ, φ⟩` of a family `Λ_s = Q_s g` with a test function is `∫ g φ`. -/
theorem pairing_eq_integral_of_bound {g φ : ParabolicSpace → ℝ} (hg : Continuous g) {B : ℝ}
    {n : ℕ} (hB : ∀ u, |g u| ≤ B * (1 + parabolicNorm u) ^ n) (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) {Λ : ℝ → ParabolicSpace → ℝ}
    (hΛ : ∀ s, 0 < s → Λ s = parabolicSemigroup.apply s g) :
    parabolicSemigroup.pairing Λ φ = ∫ z, g z * φ z := by
  refine parabolicSemigroup.pairing_eq_of_tendsto
    ((tendsto_integral_apply_mul hg hB hφ hφc).congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [hΛ s hs]

end RegularityStructures

end
