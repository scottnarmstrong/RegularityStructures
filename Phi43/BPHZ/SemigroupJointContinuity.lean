/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Polynomial.Model.Growth
public import RegularityStructures.Analysis.Parabolic.TestFunction
import Mathlib.Tactic

/-!
# Joint continuity of the regularisation `(t, z) ↦ Q_t g (z)`

For a continuous function `g` of polynomial growth (`PolyBounded g`), the regularisation
`Q_t g (z) = ∫ q_t(z - w) g(w) dw` is jointly continuous in `(t, z)` on `t > 0`
(`continuousOn_semigroup_apply`).  By the exact parabolic scaling of the kernel,
`Q_t g (z) = ∫ q_1(b) g(z - S_{t^{1/4}} b) db` (`semigroup_apply_eq_dilate`); dominated convergence
applies with the dominating function `|q_1(b)| (1 + ‖b‖)^n`, locally uniformly in `(t, z)`.
-/

public section

open MeasureTheory Filter Topology

namespace RegularityStructures

/-- The regularisation in rescaled form: `Q_t g (z) = ∫ q_1(b) g(z - S_{t^{1/4}} b) db`. -/
theorem semigroup_apply_eq_dilate (g : ParabolicSpace → ℝ) {t : ℝ} (ht : 0 < t)
    (z : ParabolicSpace) :
    parabolicSemigroup.apply t g z =
      ∫ b, parabolicKernel 1 b * g (z - parabolicDilate (t ^ (1 / 4 : ℝ)) b) := by
  have hd : 0 < t ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos ht _
  have h1 : parabolicSemigroup.apply t g z = ∫ a, parabolicKernel t a * g (z - a) := by
    unfold RegularisingSemigroup.apply
    change ∫ y, parabolicKernel t (z - y) * g y = _
    have : (volume : Measure ParabolicSpace).IsAddHaarMeasure :=
      (inferInstance : (volume.prod volume : Measure ParabolicSpace).IsAddHaarMeasure)
    have h := integral_sub_left_eq_self (fun a => parabolicKernel t a * g (z - a)) volume z
    simp only [sub_sub_cancel] at h
    exact h
  rw [h1]
  have h2 := integral_comp_parabolicDilate (fun a => parabolicKernel t a * g (z - a)) hd
  have h5 : (t ^ (1 / 4 : ℝ)) ^ 5 = t ^ (5 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]; norm_num
  have h6 : ∀ b, parabolicKernel t (parabolicDilate (t ^ (1 / 4 : ℝ)) b) =
      t ^ (-(5 / 4 : ℝ)) * parabolicKernel 1 b := fun b => by
    rw [parabolicKernel_eq_scale ht]
    congr 2
    have : t ^ (-(1 / 4 : ℝ)) = (t ^ (1 / 4 : ℝ))⁻¹ := Real.rpow_neg ht.le _
    rw [this, parabolicDilate_inv_parabolicDilate hd.ne']
  have h7 : ∀ b, parabolicKernel t (parabolicDilate (t ^ (1 / 4 : ℝ)) b) *
      g (z - parabolicDilate (t ^ (1 / 4 : ℝ)) b) =
      t ^ (-(5 / 4 : ℝ)) * (parabolicKernel 1 b * g (z - parabolicDilate (t ^ (1 / 4 : ℝ)) b)) :=
    fun b => by rw [h6]; ring
  simp only [h7, integral_const_mul] at h2
  rw [h5] at h2
  have h8 : t ^ (5 / 4 : ℝ) * t ^ (-(5 / 4 : ℝ)) = 1 := by
    rw [← Real.rpow_add ht]; simp
  have h9 : ∫ a, parabolicKernel t a * g (z - a) =
      t ^ (5 / 4 : ℝ) * (t ^ (-(5 / 4 : ℝ)) * ∫ b, parabolicKernel 1 b *
        g (z - parabolicDilate (t ^ (1 / 4 : ℝ)) b)) := by
    rw [h2, ← mul_assoc, mul_inv_cancel₀ (Real.rpow_pos_of_pos ht _).ne', one_mul]
  rw [h9, ← mul_assoc, h8, one_mul]

/-- **Joint continuity of `(t, z) ↦ Q_t g (z)`** for `t > 0`. -/
theorem continuousOn_semigroup_apply {g : ParabolicSpace → ℝ} (hg : PolyBounded g)
    (hc : Continuous g) :
    ContinuousOn (fun p : ℝ × ParabolicSpace => parabolicSemigroup.apply p.1 g p.2)
      (Set.Ioi 0 ×ˢ Set.univ) := by
  intro p0 hp0
  have ht0 : 0 < p0.1 := hp0.1
  obtain ⟨-, B, n, hB⟩ := hg
  have hint := integrable_abs_parabolicKernel_mul_pow (t := 1) one_pos n
  have hB0 : 0 ≤ B := nonneg_of_bound hB
  set F : ℝ × ParabolicSpace → ParabolicSpace → ℝ := fun p b =>
    parabolicKernel 1 b * g (p.2 - parabolicDilate (p.1 ^ (1 / 4 : ℝ)) b) with hF
  set dmax : ℝ := (2 * p0.1) ^ (1 / 4 : ℝ) with hdmax
  set R : ℝ := 1 + parabolicNorm p0.2 + 1 with hR
  have hR0 : 0 ≤ R := by have := parabolicNorm_nonneg p0.2; rw [hR]; linarith
  have hd0 : 0 ≤ dmax := Real.rpow_nonneg (by linarith) _
  have hnear : ∀ᶠ p in 𝓝 p0, p.1 ∈ Set.Ioo (p0.1 / 2) (2 * p0.1) ∧ parabolicNorm p.2 < parabolicNorm p0.2 + 1 := by
    have h1 : ∀ᶠ p : ℝ × ParabolicSpace in 𝓝 p0, p.1 ∈ Set.Ioo (p0.1 / 2) (2 * p0.1) :=
      (continuous_fst.continuousAt (x := p0)).eventually (Ioo_mem_nhds (by linarith) (by linarith))
    have h2 : ∀ᶠ p : ℝ × ParabolicSpace in 𝓝 p0, parabolicNorm p.2 < parabolicNorm p0.2 + 1 :=
      (continuous_parabolicNorm.comp continuous_snd).continuousAt.eventually
        (Iio_mem_nhds (show parabolicNorm p0.2 < parabolicNorm p0.2 + 1 by linarith))
    exact h1.and h2
  have hcont : ContinuousAt (fun p : ℝ × ParabolicSpace => ∫ b, F p b) p0 := by
    refine continuousAt_of_dominated (bound := fun b => B * (R + dmax * parabolicNorm b) ^ n *
      |parabolicKernel 1 b|) ?_ ?_ ?_ ?_
    · refine hnear.mono fun p _ => ?_
      refine ((measurable_parabolicKernel 1).mul ?_).aestronglyMeasurable
      exact hc.measurable.comp (measurable_const.sub
        ((measurable_parabolicDilate _)))
    · refine hnear.mono fun p hp => Filter.Eventually.of_forall fun b => ?_
      obtain ⟨⟨hp1, hp2⟩, hp3⟩ := hp
      have hpos : 0 < p.1 := by linarith
      have hdle : p.1 ^ (1 / 4 : ℝ) ≤ dmax := Real.rpow_le_rpow hpos.le hp2.le (by norm_num)
      have hdn : 0 ≤ p.1 ^ (1 / 4 : ℝ) := Real.rpow_nonneg hpos.le _
      have hnorm : parabolicNorm (p.2 - parabolicDilate (p.1 ^ (1 / 4 : ℝ)) b) ≤
          R - 1 + dmax * parabolicNorm b := by
        have h := parabolicNorm_add_le p.2 (-parabolicDilate (p.1 ^ (1 / 4 : ℝ)) b)
        rw [parabolicNorm_neg, parabolicNorm_parabolicDilate hdn] at h
        rw [sub_eq_add_neg]
        have := mul_le_mul_of_nonneg_right hdle (parabolicNorm_nonneg b)
        rw [hR]; linarith
      have hgb := hB (p.2 - parabolicDilate (p.1 ^ (1 / 4 : ℝ)) b)
      have hpow : (1 + parabolicNorm (p.2 - parabolicDilate (p.1 ^ (1 / 4 : ℝ)) b)) ^ n ≤
          (R + dmax * parabolicNorm b) ^ n :=
        pow_le_pow_left₀ (by have := parabolicNorm_nonneg (p.2 - parabolicDilate (p.1 ^ (1 / 4 : ℝ)) b); linarith)
          (by linarith) n
      simp only [hF, Real.norm_eq_abs, abs_mul]
      calc |parabolicKernel 1 b| * |g (p.2 - parabolicDilate (p.1 ^ (1 / 4 : ℝ)) b)|
          ≤ |parabolicKernel 1 b| * (B * (R + dmax * parabolicNorm b) ^ n) :=
            mul_le_mul_of_nonneg_left (hgb.trans (mul_le_mul_of_nonneg_left hpow hB0))
              (abs_nonneg _)
        _ = _ := by ring
    · have hm : ∀ b, B * (R + dmax * parabolicNorm b) ^ n * |parabolicKernel 1 b| ≤
          B * (max R 1 * max dmax 1) ^ n * ((|parabolicKernel 1 b| * (1 + parabolicNorm b) ^ n)) := by
        intro b
        have hb := parabolicNorm_nonneg b
        have hle : R + dmax * parabolicNorm b ≤ max R 1 * max dmax 1 * (1 + parabolicNorm b) := by
          have h1 : R ≤ max R 1 := le_max_left _ _
          have h2 : dmax ≤ max dmax 1 := le_max_left _ _
          have h3 : (1 : ℝ) ≤ max R 1 := le_max_right _ _
          have h4 : (1 : ℝ) ≤ max dmax 1 := le_max_right _ _
          nlinarith [mul_nonneg hb (sub_nonneg.2 h2), mul_nonneg hd0 hb, mul_nonneg (sub_nonneg.2 h1) hb]
        have hpw : (R + dmax * parabolicNorm b) ^ n ≤
            (max R 1 * max dmax 1) ^ n * (1 + parabolicNorm b) ^ n := by
          rw [← mul_pow]
          exact pow_le_pow_left₀ (by positivity) hle n
        calc B * (R + dmax * parabolicNorm b) ^ n * |parabolicKernel 1 b|
            ≤ B * ((max R 1 * max dmax 1) ^ n * (1 + parabolicNorm b) ^ n) * |parabolicKernel 1 b| := by
              gcongr
          _ = _ := by ring
      refine (hint.const_mul (B * (max R 1 * max dmax 1) ^ n)).mono' ?_ ?_
      · exact ((measurable_const.mul ((measurable_const.add
          (continuous_parabolicNorm.measurable.const_mul dmax)).pow_const n)).mul
          (continuous_abs.measurable.comp (measurable_parabolicKernel 1))).aestronglyMeasurable
      · refine Filter.Eventually.of_forall fun b => ?_
        have hbn := parabolicNorm_nonneg b
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg hB0
          (pow_nonneg (add_nonneg hR0 (mul_nonneg hd0 hbn)) n)) (abs_nonneg _))]
        exact hm b
    · refine Filter.Eventually.of_forall fun b => ?_
      have h1 : Continuous (fun p : ℝ × ParabolicSpace => p.2 - parabolicDilate (p.1 ^ (1 / 4 : ℝ)) b) := by
        unfold parabolicDilate
        have hr : Continuous (fun p : ℝ × ParabolicSpace => p.1 ^ (1 / 4 : ℝ)) :=
          continuous_fst.rpow_const (fun _ => Or.inr (by norm_num))
        exact continuous_snd.sub (((hr.pow 2).mul continuous_const).prodMk
          (hr.smul continuous_const))
      exact (continuous_const.mul (hc.comp h1)).continuousAt
  refine ContinuousAt.continuousWithinAt (hcont.congr_of_eventuallyEq ?_)
  filter_upwards [hnear] with p hp
  exact semigroup_apply_eq_dilate g (by linarith [hp.1.1]) p.2

end RegularityStructures

end
