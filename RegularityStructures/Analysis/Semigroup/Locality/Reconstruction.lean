/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.Reconstruction
public import RegularityStructures.Analysis.Semigroup.Locality.Tail

/-!
# Locality of the germ reconstruction, up to kernel tails

Hairer's reconstruction is exactly local ([Hai14, Lemma 6.7, Proposition 7.2],
arXiv:1303.5113v4). In the `Q`-form used here the kernels have non-compact support, so locality
holds up to the kernel tails of `RegularityStructures.Analysis.Semigroup.Locality.Tail`.

If `F` is a coherent germ (`IsCoherent F γ A C`, `γ > 0`) with Besov-type diagonal bound
`|F_y(t, y)| ≤ B t^{α/ℓ}` for `α ≤ 0`, and `F y = 0` as a family whenever `d(y, x₀) < r`, then
for `0 < t ≤ 1` and `k ≥ 0`
`|RF_t(x₀)| ≤ M₀ c C t^{γ/ℓ} + 2^{-α/ℓ} M_k (B + c C) t^{α/ℓ} (t^{1/ℓ}/r)^k`.

The proof is `RF_t = Q_{t/2} RF_{t/2}`: on the ball `|RF_{t/2}| = |RF_{t/2} - diag| ≤ c C (t/2)^{γ/ℓ}`
since `diag = 0`; outside, `|RF_{t/2}| ≤ (B + c C)(t/2)^{α/ℓ}` (`abs_reconstruct_le`) and the
tail (a pointwise Markov bound) is used.

* `abs_reconstruct_le_of_vanishing`: the one-germ estimate;
* `abs_reconstruct_sub_reconstruct_le_of_eq`: if `F = G` as families near `x₀`, then
  `|RF_t(x₀) - RG_t(x₀)| ≤ M₀ c (C_F + C_G) t^{γ/ℓ} +
    2^{-α/ℓ} M_k (B_F + B_G + c (C_F + C_G)) t^{α/ℓ} (t^{1/ℓ}/r)^k`.
-/

public section

open MeasureTheory Filter Set

namespace RegularityStructures.RegularisingSemigroup

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} (K : RegularisingSemigroup E μ)
  [SFinite μ] {F G : E → ℝ → E → ℝ}

/-- Pointwise form of the locality bound for `RF_s`, `s ≤ 1`: a constant on the ball and a
polynomial growth `(d/r)^k` outside. -/
theorem abs_reconstruct_le_of_vanishing_pointwise (hF : K.IsGerm F) {γ : ℝ} (hγ : 0 < γ)
    {A : Finset ℝ} (hA : ∀ a ∈ A, a < γ) {C : ℝ} (hC : 0 ≤ C) (hcoh : K.IsCoherent F γ A C)
    {α B : ℝ} (hα : α ≤ 0)
    (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ y, |F y t y| ≤ B * t ^ (α / K.order))
    {x₀ : E} {r : ℝ} (hr : 0 < r) (hzero : ∀ y, K.scaleDist y x₀ < r → F y = 0)
    {k : ℝ} (hk : 0 ≤ k) {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) (y : E) :
    |K.reconstruct F s y| ≤ K.reconstructionConst γ A * C * s ^ (γ / K.order) +
      (B + K.reconstructionConst γ A * C) * s ^ (α / K.order) *
        (K.scaleDist y x₀ / r) ^ k := by
  have hB0 : 0 ≤ B + K.reconstructionConst γ A * C := by
    have h := (abs_nonneg _).trans (hB s hs y)
    have h1 : 0 ≤ B := (mul_nonneg_iff_of_pos_right (Real.rpow_pos_of_pos hs.1 _)).1 h
    exact add_nonneg h1 (mul_nonneg (K.reconstructionConst_nonneg hγ.le A) hC)
  have hq : 0 ≤ (K.scaleDist y x₀ / r) ^ k :=
    Real.rpow_nonneg (div_nonneg (K.scaleDist_nonneg _ _) hr.le) _
  have hT : 0 ≤ (B + K.reconstructionConst γ A * C) * s ^ (α / K.order) *
      (K.scaleDist y x₀ / r) ^ k :=
    mul_nonneg (mul_nonneg hB0 (Real.rpow_nonneg hs.1.le _)) hq
  by_cases hy : K.scaleDist y x₀ < r
  · have h := K.abs_reconstruct_sub_diag_le hF hγ hA hC hcoh hs y
    rw [hzero y hy] at h
    simp only [Pi.zero_apply, sub_zero] at h
    linarith
  · have h1 : 1 ≤ (K.scaleDist y x₀ / r) ^ k :=
      Real.one_le_rpow ((one_le_div hr).2 (not_lt.1 hy)) hk
    have h2 := K.abs_reconstruct_le hF hγ hA hC hcoh hα hB hs y
    have h3 : 0 ≤ K.reconstructionConst γ A * C * s ^ (γ / K.order) :=
      mul_nonneg (mul_nonneg (K.reconstructionConst_nonneg hγ.le A) hC)
        (Real.rpow_nonneg hs.1.le _)
    calc |K.reconstruct F s y| ≤ (B + K.reconstructionConst γ A * C) * s ^ (α / K.order) := h2
      _ = (B + K.reconstructionConst γ A * C) * s ^ (α / K.order) * 1 := (mul_one _).symm
      _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left h1
          (mul_nonneg hB0 (Real.rpow_nonneg hs.1.le (α / K.order)))
        linarith

/-- **Locality of the reconstruction up to kernel tails.** -/
theorem abs_reconstruct_le_of_vanishing (hF : K.IsGerm F) {γ : ℝ} (hγ : 0 < γ)
    {A : Finset ℝ} (hA : ∀ a ∈ A, a < γ) {C : ℝ} (hC : 0 ≤ C) (hcoh : K.IsCoherent F γ A C)
    {α B : ℝ} (hα : α ≤ 0)
    (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ y, |F y t y| ≤ B * t ^ (α / K.order))
    {x₀ : E} {r : ℝ} (hr : 0 < r) (hzero : ∀ y, K.scaleDist y x₀ < r → F y = 0)
    {k : ℝ} (hk : 0 ≤ k) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    |K.reconstruct F t x₀| ≤ K.momentConst 0 * (K.reconstructionConst γ A * C) * t ^ (γ / K.order) +
      2 ^ (-α / K.order) * K.momentConst k * (B + K.reconstructionConst γ A * C) *
        t ^ (α / K.order) * (t ^ (1 / K.order) / r) ^ k := by
  have hℓ := K.order_pos
  set c := K.reconstructionConst γ A with hc
  have hc0 : 0 ≤ c := K.reconstructionConst_nonneg hγ.le A
  have hs : t / 2 ∈ Ioc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hs0 := hs.1
  set s := t / 2 with hsdef
  have hB' : 0 ≤ B + c * C := by
    have h := (abs_nonneg _).trans (hB s hs x₀)
    exact add_nonneg ((mul_nonneg_iff_of_pos_right (Real.rpow_pos_of_pos hs0 _)).1 h)
      (mul_nonneg hc0 hC)
  set a := c * C * s ^ (γ / K.order) with ha
  set b := (B + c * C) * s ^ (α / K.order) with hb
  have hpt := K.abs_reconstruct_le_of_vanishing_pointwise hF hγ hA hC hcoh hα hB hr hzero hk hs
  have hmem := K.reconstruct_mem hF hγ hA hC hcoh
  have heq : K.reconstruct F t x₀ = K.apply s (K.reconstruct F s) x₀ := by
    rw [K.apply_reconstruct hF hγ hA hC hcoh hs0 hs0]
    congr 1; rw [hsdef]; ring
  have hi : Integrable (fun y => |K.kernel s x₀ y| * (a + b * (K.scaleDist y x₀ / r) ^ k)) μ := by
    have h1 := (K.integrable_kernel hs0 x₀).abs.mul_const a
    have h2 := (K.integrable_abs_kernel_mul_div_pow hs0 hk hr x₀).const_mul b
    exact (h1.add h2).congr (Filter.Eventually.of_forall fun y => by
      simp only [Pi.add_apply]; ring)
  have hint := norm_integral_le_of_norm_le hi (f := fun y => K.kernel s x₀ y *
    K.reconstruct F s y) (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hpt y) (abs_nonneg _))
  rw [Real.norm_eq_abs] at hint
  have hsplit : ∫ y, |K.kernel s x₀ y| * (a + b * (K.scaleDist y x₀ / r) ^ k) ∂μ =
      (∫ y, |K.kernel s x₀ y| ∂μ) * a +
        b * ∫ y, |K.kernel s x₀ y| * (K.scaleDist y x₀ / r) ^ k ∂μ := by
    have h1 := (K.integrable_kernel hs0 x₀).abs.mul_const a
    have h2 := (K.integrable_abs_kernel_mul_div_pow hs0 hk hr x₀).const_mul b
    have : (fun y => |K.kernel s x₀ y| * (a + b * (K.scaleDist y x₀ / r) ^ k)) =
        fun y => |K.kernel s x₀ y| * a + b * (|K.kernel s x₀ y| *
          (K.scaleDist y x₀ / r) ^ k) := by
      ext y; ring
    rw [this, integral_add h1 h2, integral_mul_const, integral_const_mul]
  have e0 := K.integral_abs_kernel_le hs0 x₀
  have e1 := K.integral_abs_kernel_mul_div_pow_le hs0 hk hr x₀
  have ha0 : 0 ≤ a := mul_nonneg (mul_nonneg hc0 hC) (Real.rpow_nonneg hs0.le _)
  have hb0 : 0 ≤ b := mul_nonneg hB' (Real.rpow_nonneg hs0.le _)
  have hstep : |K.reconstruct F t x₀| ≤ K.momentConst 0 * a +
      b * (K.momentConst k * s ^ (k / K.order) * r ^ (-k)) := by
    rw [heq]
    refine (le_trans (by simpa [apply] using hint) (hsplit.le.trans ?_))
    have := mul_le_mul_of_nonneg_right e0 ha0
    have := mul_le_mul_of_nonneg_left e1 hb0
    linarith
  refine hstep.trans ?_
  -- compare with the stated bound
  have hts : s ≤ t := by linarith [ht.1]
  have hγ' : s ^ (γ / K.order) ≤ t ^ (γ / K.order) :=
    Real.rpow_le_rpow hs0.le hts (div_nonneg hγ.le hℓ.le)
  have hk' : s ^ (k / K.order) ≤ t ^ (k / K.order) :=
    Real.rpow_le_rpow hs0.le hts (div_nonneg hk hℓ.le)
  have hα' : s ^ (α / K.order) = 2 ^ (-α / K.order) * t ^ (α / K.order) := by
    rw [hsdef, Real.div_rpow ht.1.le (by norm_num), div_eq_mul_inv, ← Real.rpow_neg
      (by norm_num : (0 : ℝ) ≤ 2), neg_div]
    ring
  have hR : (t ^ (1 / K.order) / r) ^ k = t ^ (k / K.order) * r ^ (-k) := by
    rw [Real.div_rpow (Real.rpow_nonneg ht.1.le _) hr.le, ← Real.rpow_mul ht.1.le,
      Real.rpow_neg hr.le, div_eq_mul_inv, one_div, inv_mul_eq_div]
  have hM0 := K.momentConst_nonneg 0
  have hMk := K.momentConst_nonneg k
  have hr' : 0 ≤ r ^ (-k) := Real.rpow_nonneg hr.le _
  have t1 : K.momentConst 0 * a ≤ K.momentConst 0 * (c * C) * t ^ (γ / K.order) := by
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hγ' (mul_nonneg hc0 hC)) hM0
    rw [ha]
    linarith
  have t2 : b * (K.momentConst k * s ^ (k / K.order) * r ^ (-k)) ≤
      2 ^ (-α / K.order) * K.momentConst k * (B + c * C) * t ^ (α / K.order) *
        (t ^ (1 / K.order) / r) ^ k := by
    rw [hR, hb, hα']
    have h2 : 0 ≤ (2 : ℝ) ^ (-α / K.order) := Real.rpow_nonneg (by norm_num) _
    have : K.momentConst k * s ^ (k / K.order) * r ^ (-k) ≤
        K.momentConst k * t ^ (k / K.order) * r ^ (-k) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk' hMk) hr'
    calc (B + c * C) * (2 ^ (-α / K.order) * t ^ (α / K.order)) *
          (K.momentConst k * s ^ (k / K.order) * r ^ (-k))
        ≤ (B + c * C) * (2 ^ (-α / K.order) * t ^ (α / K.order)) *
          (K.momentConst k * t ^ (k / K.order) * r ^ (-k)) :=
          mul_le_mul_of_nonneg_left this (mul_nonneg hB' (mul_nonneg h2
            (Real.rpow_nonneg ht.1.le _)))
      _ = _ := by ring
  linarith

/-- **Two-germ locality**: if `F y = G y` as families for `d(y, x₀) < r`, the reconstructions at
`x₀` differ by at most the same bound with `C = C_F + C_G`, `B = B_F + B_G`. -/
theorem abs_reconstruct_sub_reconstruct_le_of_eq (hF : K.IsGerm F) (hG : K.IsGerm G) {γ : ℝ}
    (hγ : 0 < γ) {A : Finset ℝ} (hA : ∀ a ∈ A, a < γ) {CF CG : ℝ} (hCF : 0 ≤ CF)
    (hCG : 0 ≤ CG) (hcF : K.IsCoherent F γ A CF) (hcG : K.IsCoherent G γ A CG)
    {α BF BG : ℝ} (hα : α ≤ 0)
    (hBF : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ y, |F y t y| ≤ BF * t ^ (α / K.order))
    (hBG : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ y, |G y t y| ≤ BG * t ^ (α / K.order))
    {x₀ : E} {r : ℝ} (hr : 0 < r) (heq : ∀ y, K.scaleDist y x₀ < r → F y = G y)
    {k : ℝ} (hk : 0 ≤ k) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    |K.reconstruct F t x₀ - K.reconstruct G t x₀| ≤
      K.momentConst 0 * (K.reconstructionConst γ A * (CF + CG)) * t ^ (γ / K.order) +
      2 ^ (-α / K.order) * K.momentConst k *
        (BF + BG + K.reconstructionConst γ A * (CF + CG)) *
        t ^ (α / K.order) * (t ^ (1 / K.order) / r) ^ k := by
  have hGs := hG.smul (-1)
  have hcGs := hcG.smul (-1)
  have hH := hF.add hGs
  have hcH := hcF.add hcGs
  have hC : 0 ≤ CF + |(-1 : ℝ)| * CG := add_nonneg hCF (mul_nonneg (abs_nonneg _) hCG)
  have hrec : K.reconstruct (fun y => F y + (-1 : ℝ) • G y) =
      K.reconstruct F - K.reconstruct G := by
    have e : (fun y => F y - G y) = fun y => F y + (-1 : ℝ) • G y := by
      funext y; simp [sub_eq_add_neg]
    rw [← e]; exact K.reconstruct_sub hF hG hγ hA hCF hCG hcF hcG
  have hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ y, |(fun y => F y + (-1 : ℝ) • G y) y t y| ≤
      (BF + BG) * t ^ (α / K.order) := by
    intro t ht y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc |F y t y + -1 * G y t y| ≤ |F y t y| + |G y t y| := by
          rw [neg_one_mul]; exact (abs_sub _ _)
      _ ≤ _ := by linarith [hBF t ht y, hBG t ht y]
  have hz : ∀ y, K.scaleDist y x₀ < r → (fun y => F y + (-1 : ℝ) • G y) y = 0 := by
    intro y hy
    simp only [heq y hy]
    ext1 u; ext1 z
    simp
  have h := K.abs_reconstruct_le_of_vanishing hH hγ hA hC hcH hα hB hr hz hk ht
  rw [hrec] at h
  simp only [abs_neg, abs_one, one_mul] at h
  simpa [Pi.sub_apply, add_assoc] using h

end RegularityStructures.RegularisingSemigroup

end
