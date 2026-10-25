/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsComparisonHairerMollifiedBound
public import Phi43.BPHZ.SingularConvolution
public import Phi43.Stochastic.ConstantsComparisonDefinitions

/-!
# Singular bounds for Hairer's mollified covariance

For `K_ε = hairerMollifiedKernel N ρ ε` and `Q_ε(z) = ∫ K_ε(z + w) K_ε(w) dw`, we prove
`|Q_ε z| ≲ s(z)⁻¹` (via the convolution estimate of `SingularConvolution`, [Hai14, Lemma 10.14])
and the uniform bound `|Q_ε z| ≲ (s(z) + ε)⁻¹`, valid also at `s z = 0`.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

private theorem hairerCov_size_neg_le (w : SpaceTime) :
    torusParabolicSize (-w) ≤ 2 * torusParabolicSize w := by
  unfold torusParabolicSize
  change √|(-w.1)| + torusSpatialNorm (-w.2) ≤ 2 * (√|w.1| + torusSpatialNorm w.2)
  rw [abs_neg]
  have := torusSpatialNorm_neg_le w.2
  have := Real.sqrt_nonneg |w.1|
  have := torusSpatialNorm_nonneg w.2
  linarith

private theorem hairerCov_ae_size_pos : ∀ᵐ w : SpaceTime ∂volume, 0 < torusParabolicSize w := by
  rw [ae_iff]
  have h := volume_torusParabolicBall_le_global (le_refl (0 : ℝ))
  have h0 : volume {z : SpaceTime | torusParabolicSize z ≤ 0} = 0 :=
    nonpos_iff_eq_zero.1 (by simpa using h)
  exact measure_mono_null (fun w hw => not_lt.1 hw) h0

private theorem hairerCov_rpow_neg_three_le {s ε : ℝ} (hs : 0 < s) (hε : 0 < ε) :
    (s + ε) ^ (-(3 : ℝ)) ≤ s ^ (-(3 : ℝ)) :=
  Real.rpow_le_rpow_of_nonpos hs (by linarith) (by norm_num)

private theorem hairerCov_inv_le_two_inv {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : b ≤ 2 * a) :
    a⁻¹ ≤ 2 * b⁻¹ := by
  rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ ha hb]
  linarith

private theorem hairerCov_rpow_three_eight : ((2 : ℝ) ^ (3 : ℝ)) = 8 := by
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

/-- Pointwise algebra for the product of two bounded values. -/
private theorem hairerCov_mul_le {C x y u v : ℝ} (hC : 0 ≤ C) (hx : |x| ≤ C * u)
    (hy : |y| ≤ C * v) (hu : 0 ≤ u) (_hv : 0 ≤ v) :
    |x * y| ≤ C ^ 2 / 2 * (u ^ 2 + v ^ 2) := by
  rw [abs_mul]
  have h1 : |x| * |y| ≤ (C * u) * (C * v) :=
    mul_le_mul hx hy (abs_nonneg _) (mul_nonneg hC hu)
  have h2 : 0 ≤ (C * (u - v)) ^ 2 := sq_nonneg _
  nlinarith

/-- The squared weight `(s + ε)⁻⁶` is integrable with integral `≲ ε⁻¹`. -/
private theorem hairerCov_sq_weight {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun w : SpaceTime => ((torusParabolicSize w + ε) ^ (-(3 : ℝ))) ^ 2) ∧
      ∫ w : SpaceTime, ((torusParabolicSize w + ε) ^ (-(3 : ℝ))) ^ 2 ≤
        136 * ε ^ (-(1 : ℝ)) := by
  set M : SpaceTime → ℝ := fun w => ε ^ (-(3 : ℝ)) * singularLocalWeight 3 ε w +
    singularTailWeight 6 ε w with hMdef
  have hM : Integrable M :=
    ((integrable_singularLocalWeight (p := 3) (a := ε) (by norm_num) (by norm_num) hε).const_mul
      _).add (integrable_singularTailWeight (p := 6) (e := ε) (by norm_num) hε)
  have hpt : ∀ w : SpaceTime, 0 < torusParabolicSize w →
      ((torusParabolicSize w + ε) ^ (-(3 : ℝ))) ^ 2 ≤ M w := by
    intro w hw
    set s := torusParabolicSize w with hs
    have hG0 : 0 ≤ (s + ε) ^ (-(3 : ℝ)) := Real.rpow_nonneg (by linarith) _
    have hGs : (s + ε) ^ (-(3 : ℝ)) ≤ s ^ (-(3 : ℝ)) := hairerCov_rpow_neg_three_le hw hε
    have hGe : (s + ε) ^ (-(3 : ℝ)) ≤ ε ^ (-(3 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hε (by linarith) (by norm_num)
    by_cases h : s ≤ ε
    · have hL : singularLocalWeight 3 ε w = s ^ (-(3 : ℝ)) := by
        simp [singularLocalWeight, ← hs, hw, h]
      have hT : singularTailWeight 6 ε w = 0 := by
        simp [singularTailWeight, ← hs, not_lt.2 h]
      simp only [hMdef, hL, hT, add_zero]
      rw [sq]
      exact mul_le_mul hGe hGs hG0 (Real.rpow_nonneg hε.le _)
    · have hL : singularLocalWeight 3 ε w = 0 := by
        simp [singularLocalWeight, ← hs, h]
      have hT : singularTailWeight 6 ε w = s ^ (-(6 : ℝ)) := by
        simp [singularTailWeight, ← hs, lt_of_not_ge h]
      simp only [hMdef, hL, hT, mul_zero, zero_add]
      have : s ^ (-(6 : ℝ)) = s ^ (-(3 : ℝ)) * s ^ (-(3 : ℝ)) := by
        rw [← Real.rpow_add hw]; norm_num
      rw [this, sq]
      exact mul_le_mul hGs hGs hG0 (Real.rpow_nonneg hw.le _)
  have hae : ∀ᵐ w : SpaceTime ∂volume,
      ((torusParabolicSize w + ε) ^ (-(3 : ℝ))) ^ 2 ≤ M w := by
    filter_upwards [hairerCov_ae_size_pos] with w hw using hpt w hw
  have hmeas : Measurable fun w : SpaceTime =>
      ((torusParabolicSize w + ε) ^ (-(3 : ℝ))) ^ 2 :=
    ((measurable_torusParabolicSize.add_const ε).pow_const _).pow_const 2
  have hint : Integrable (fun w : SpaceTime =>
      ((torusParabolicSize w + ε) ^ (-(3 : ℝ))) ^ 2) := by
    refine Integrable.mono' hM hmeas.aestronglyMeasurable ?_
    filter_upwards [hae] with w hw
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hw
  refine ⟨hint, ?_⟩
  have hnn : ∀ w : SpaceTime, 0 ≤ ((torusParabolicSize w + ε) ^ (-(3 : ℝ))) ^ 2 :=
    fun _ => sq_nonneg _
  have h1 : ∫ w : SpaceTime, ((torusParabolicSize w + ε) ^ (-(3 : ℝ))) ^ 2 ≤ ∫ w, M w :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall hnn) hM hae
  have hLi := integrable_singularLocalWeight (p := 3) (a := ε) (by norm_num) (by norm_num) hε
  have hTi := integrable_singularTailWeight (p := 6) (e := ε) (by norm_num) hε
  have hL := integral_singularLocalWeight_le (p := 3) (a := ε) (by norm_num) (by norm_num) hε
  have hT := integral_singularTailWeight_le (p := 6) (e := ε) (by norm_num) hε
  have h2 : ∫ w, M w = ε ^ (-(3 : ℝ)) * (∫ w, singularLocalWeight 3 ε w) +
      ∫ w, singularTailWeight 6 ε w := by
    simp only [hMdef]
    rw [integral_add (hLi.const_mul _) hTi, integral_const_mul]
  have e1 : ε ^ (-(3 : ℝ)) * ε ^ ((5 : ℝ) - 3) = ε ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_add hε]; norm_num
  have e2 : ε ^ ((5 : ℝ) - 6) = ε ^ (-(1 : ℝ)) := by norm_num
  have hc : 0 ≤ ε ^ (-(3 : ℝ)) := Real.rpow_nonneg hε.le _
  calc ∫ w : SpaceTime, ((torusParabolicSize w + ε) ^ (-(3 : ℝ))) ^ 2 ≤ ∫ w, M w := h1
    _ = ε ^ (-(3 : ℝ)) * (∫ w, singularLocalWeight 3 ε w) +
      ∫ w, singularTailWeight 6 ε w := h2
    _ ≤ ε ^ (-(3 : ℝ)) * (80 / (5 - 3) * ε ^ ((5 : ℝ) - 3)) +
        16 * 6 / (6 - 5) * ε ^ ((5 : ℝ) - 6) := add_le_add (mul_le_mul_of_nonneg_left hL hc) hT
    _ = 80 / (5 - 3) * (ε ^ (-(3 : ℝ)) * ε ^ ((5 : ℝ) - 3)) +
        16 * 6 / (6 - 5) * ε ^ ((5 : ℝ) - 6) := by ring
    _ = 136 * ε ^ (-(1 : ℝ)) := by rw [e1, e2]; norm_num; ring

/-- The covariance is `≲ ε⁻¹` uniformly in `z`. -/
private theorem hairerCov_abs_le_inv_eps (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ)
    (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ z : SpaceTime,
      |hairerCovariance N ρ ε z| ≤ C * ε ^ (-(1 : ℝ)) := by
  obtain ⟨C0, hC0, hK⟩ := hairerMollifiedKernel_singular_bound ρ hρ N
  refine ⟨136 * C0 ^ 2, by positivity, ?_⟩
  intro ε hε hε1 z
  obtain ⟨hGi, hGI⟩ := hairerCov_sq_weight hε
  set G : SpaceTime → ℝ := fun w => ((torusParabolicSize w + ε) ^ (-(3 : ℝ))) ^ 2 with hG
  have hGi' : Integrable (fun w => G (z + w)) :=
    (measurePreserving_add_left volume z).integrable_comp_of_integrable hGi
  have hmaj : Integrable (fun w => C0 ^ 2 / 2 * (G (z + w) + G w)) :=
    (hGi'.add hGi).const_mul _
  have hpt : ∀ w, |hairerMollifiedKernel N ρ ε (z + w) * hairerMollifiedKernel N ρ ε w| ≤
      C0 ^ 2 / 2 * (G (z + w) + G w) := fun w =>
    hairerCov_mul_le hC0 (hK hε hε1 (z + w)) (hK hε hε1 w)
      (Real.rpow_nonneg (by linarith [torusParabolicSize_nonneg (z + w)]) _)
      (Real.rpow_nonneg (by linarith [torusParabolicSize_nonneg w]) _)
  calc |hairerCovariance N ρ ε z|
      = ‖∫ w, hairerMollifiedKernel N ρ ε (z + w) * hairerMollifiedKernel N ρ ε w‖ := by
        rw [Real.norm_eq_abs]; rfl
    _ ≤ ∫ w, ‖hairerMollifiedKernel N ρ ε (z + w) * hairerMollifiedKernel N ρ ε w‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ w, C0 ^ 2 / 2 * (G (z + w) + G w) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => norm_nonneg _)
          hmaj (Filter.Eventually.of_forall fun w => ?_)
        simp only [Real.norm_eq_abs]; exact hpt w
    _ = C0 ^ 2 / 2 * (2 * ∫ w, G w) := by
        rw [integral_const_mul, integral_add hGi' hGi, integral_comp_add_left_spaceTime G z]
        ring
    _ ≤ C0 ^ 2 / 2 * (2 * (136 * ε ^ (-(1 : ℝ)))) := by
        gcongr
    _ = 136 * C0 ^ 2 * ε ^ (-(1 : ℝ)) := by ring

/-- [Hai14, §10.5]: the mollified Hairer covariance is of order `s(z)⁻¹`, uniformly in
`ε ∈ (0, 1]`. -/
theorem hairerCovariance_abs_le (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ z : SpaceTime,
      0 < torusParabolicSize z →
        |hairerCovariance N ρ ε z| ≤ C * torusParabolicSize z ^ (-(1 : ℝ)) := by
  obtain ⟨C0, hC0, hK⟩ := hairerMollifiedKernel_singular_bound ρ hρ N
  obtain ⟨Cc, hCc, hconv⟩ := abs_integral_mul_singular_le_of_gt (a := 3) (b := 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨Cc * C0 * (8 * C0), by positivity, ?_⟩
  intro ε hε hε1 z hz
  have hf : ∀ w : SpaceTime, 0 < torusParabolicSize w →
      |hairerMollifiedKernel N ρ ε w| ≤ C0 * torusParabolicSize w ^ (-(3 : ℝ)) :=
    fun w hw => (hK hε hε1 w).trans
      (mul_le_mul_of_nonneg_left (hairerCov_rpow_neg_three_le hw hε) hC0)
  have hg : ∀ w : SpaceTime, 0 < torusParabolicSize w →
      |hairerMollifiedKernel N ρ ε (-w)| ≤ 8 * C0 * torusParabolicSize w ^ (-(3 : ℝ)) := by
    intro w hw
    have h2 : torusParabolicSize w ≤ 2 * torusParabolicSize (-w) := by
      simpa using hairerCov_size_neg_le (-w)
    have hw' : 0 < torusParabolicSize (-w) := by linarith
    have hhalf : torusParabolicSize w / 2 ≤ torusParabolicSize (-w) := by linarith
    have h3 : torusParabolicSize (-w) ^ (-(3 : ℝ)) ≤
        (torusParabolicSize w / 2) ^ (-(3 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hhalf (by norm_num)
    have h4 : (torusParabolicSize w / 2) ^ (-(3 : ℝ)) = 8 * torusParabolicSize w ^ (-(3 : ℝ)) := by
      rw [Real.div_rpow hw.le (by norm_num),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) (3 : ℝ), hairerCov_rpow_three_eight,
        div_inv_eq_mul, mul_comm]
    calc |hairerMollifiedKernel N ρ ε (-w)|
        ≤ C0 * torusParabolicSize (-w) ^ (-(3 : ℝ)) := hf _ hw'
      _ ≤ C0 * (8 * torusParabolicSize w ^ (-(3 : ℝ))) :=
        mul_le_mul_of_nonneg_left (h3.trans h4.le) hC0
      _ = _ := by ring
  have hmain := hconv hC0 (by positivity) hf hg z hz
  have hexp : (5 : ℝ) - 3 - 3 = -1 := by norm_num
  rw [hexp] at hmain
  have e : hairerCovariance N ρ ε z =
      ∫ w, hairerMollifiedKernel N ρ ε (z - w) * hairerMollifiedKernel N ρ ε (-w) := by
    unfold hairerCovariance
    exact (integral_comp_sub_left_spaceTime
      (fun w => hairerMollifiedKernel N ρ ε (z + w) * hairerMollifiedKernel N ρ ε w) 0).symm.trans
      (by congr 1; funext w; simp [sub_eq_add_neg])
  calc |hairerCovariance N ρ ε z|
      = ‖∫ w, hairerMollifiedKernel N ρ ε (z - w) * hairerMollifiedKernel N ρ ε (-w)‖ := by
        rw [e, Real.norm_eq_abs]
    _ ≤ ∫ w, ‖hairerMollifiedKernel N ρ ε (z - w) * hairerMollifiedKernel N ρ ε (-w)‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ w, |hairerMollifiedKernel N ρ ε (z - w)| * |hairerMollifiedKernel N ρ ε (-w)| := by
        simp only [Real.norm_eq_abs, abs_mul]
    _ ≤ _ := hmain

/-- Uniform bound at the scale `ε`, including `s z = 0`. -/
theorem hairerCovariance_abs_le_add (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ z : SpaceTime,
      |hairerCovariance N ρ ε z| ≤ C * (torusParabolicSize z + ε) ^ (-(1 : ℝ)) := by
  obtain ⟨C1, hC1, h1⟩ := hairerCovariance_abs_le N ρ hρ
  obtain ⟨C2, hC2, h2⟩ := hairerCov_abs_le_inv_eps N ρ hρ
  refine ⟨2 * (C1 + C2), by positivity, ?_⟩
  intro ε hε hε1 z
  have hs0 := torusParabolicSize_nonneg z
  have hpos : 0 < torusParabolicSize z + ε := by linarith
  rw [Real.rpow_neg_one] at *
  by_cases h : ε ≤ torusParabolicSize z
  · have hs : 0 < torusParabolicSize z := lt_of_lt_of_le hε h
    have := h1 hε hε1 z hs
    rw [Real.rpow_neg_one] at this
    have hi := hairerCov_inv_le_two_inv hs hpos (by linarith)
    calc _ ≤ C1 * (torusParabolicSize z)⁻¹ := this
      _ ≤ C1 * (2 * (torusParabolicSize z + ε)⁻¹) := mul_le_mul_of_nonneg_left hi hC1
      _ ≤ _ := by
        have : 0 ≤ (torusParabolicSize z + ε)⁻¹ := inv_nonneg.2 hpos.le
        nlinarith
  · have := h2 hε hε1 z
    rw [Real.rpow_neg_one] at this
    have hi := hairerCov_inv_le_two_inv hε hpos (by linarith [not_le.1 h])
    calc _ ≤ C2 * ε⁻¹ := this
      _ ≤ C2 * (2 * (torusParabolicSize z + ε)⁻¹) := mul_le_mul_of_nonneg_left hi hC2
      _ ≤ _ := by
        have : 0 ≤ (torusParabolicSize z + ε)⁻¹ := inv_nonneg.2 hpos.le
        nlinarith

end RegularityStructures.Phi43

end
