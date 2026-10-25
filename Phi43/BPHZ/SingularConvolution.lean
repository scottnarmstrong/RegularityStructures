/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SingularConvolutionLayer

/-!
# Convolution of two parabolic singularities

If `|f| ≤ B₁ s^(-a)` and `|g| ≤ B₂ s^(-b)` with `0 < a, b < 5`, then `∫ |f (z - w)| |g w| dw`
is of order `s(z)^(5-a-b)` when `a + b > 5`, and bounded when `a + b < 5` (for functions
supported in `|t| ≤ 1`).  The case `a + b > 5` needs no support assumption.

Source: [Hai14] = arXiv:1303.5113v4, Lemma 10.14, (10.10), with `|s| = 5`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

private theorem rpow_neg_mul_le_add {x y a b : ℝ} (hx : 0 < x) (hy : 0 < y) (ha : 0 ≤ a)
    (hb : 0 ≤ b) : y ^ (-a) * x ^ (-b) ≤ x ^ (-(a + b)) + y ^ (-(a + b)) := by
  have hx' : 0 ≤ x ^ (-(a + b)) := Real.rpow_nonneg hx.le _
  have hy' : 0 ≤ y ^ (-(a + b)) := Real.rpow_nonneg hy.le _
  rcases le_total x y with h | h
  · have h1 : y ^ (-a) ≤ x ^ (-a) := Real.rpow_le_rpow_of_nonpos hx h (neg_nonpos.2 ha)
    have h2 : x ^ (-a) * x ^ (-b) = x ^ (-(a + b)) := by
      rw [← Real.rpow_add hx]; ring_nf
    calc
      y ^ (-a) * x ^ (-b) ≤ x ^ (-a) * x ^ (-b) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hx.le _)
      _ = x ^ (-(a + b)) := h2
      _ ≤ _ := le_add_of_nonneg_right hy'
  · have h1 : x ^ (-b) ≤ y ^ (-b) := Real.rpow_le_rpow_of_nonpos hy h (neg_nonpos.2 hb)
    have h2 : y ^ (-a) * y ^ (-b) = y ^ (-(a + b)) := by
      rw [← Real.rpow_add hy]; ring_nf
    calc
      y ^ (-a) * x ^ (-b) ≤ y ^ (-a) * y ^ (-b) :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hy.le _)
      _ = y ^ (-(a + b)) := h2
      _ ≤ _ := le_add_of_nonneg_left hx'

private theorem ae_torusParabolicSize_pos : ∀ᵐ w : SpaceTime ∂volume, 0 < torusParabolicSize w := by
  rw [ae_iff]
  have h := Phi43.volume_torusParabolicBall_le_global (le_refl (0 : ℝ))
  have h0 : volume {z : SpaceTime | torusParabolicSize z ≤ 0} = 0 := by
    exact nonpos_iff_eq_zero.1 (by simpa using h)
  refine measure_mono_null ?_ h0
  intro w hw
  exact not_lt.1 hw

private theorem ae_sub_torusParabolicSize_pos (z : SpaceTime) :
    ∀ᵐ w : SpaceTime ∂volume, 0 < torusParabolicSize (z - w) :=
  (measurePreserving_sub_left_spaceTime z).quasiMeasurePreserving.ae ae_torusParabolicSize_pos

/-- Pointwise splitting: near, mirrored-near and far parts. -/
private theorem pointwise_split {a b δ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hδ : 0 < δ)
    {w w' : SpaceTime} (hw : 0 < torusParabolicSize w) (hw' : 0 < torusParabolicSize w')
    (hsum : 2 * δ ≤ torusParabolicSize w + torusParabolicSize w') :
    torusParabolicSize w' ^ (-a) * torusParabolicSize w ^ (-b) ≤
      δ ^ (-a) * singularLocalWeight b δ w + δ ^ (-b) * singularLocalWeight a δ w' +
        singularTailWeight (a + b) δ w + singularTailWeight (a + b) δ w' := by
  have n1 := singularLocalWeight_nonneg b δ w
  have n2 := singularLocalWeight_nonneg a δ w'
  have n3 := singularTailWeight_nonneg (a + b) δ w
  have n4 := singularTailWeight_nonneg (a + b) δ w'
  have hd1 : 0 ≤ δ ^ (-a) := Real.rpow_nonneg hδ.le _
  have hd2 : 0 ≤ δ ^ (-b) := Real.rpow_nonneg hδ.le _
  by_cases hx : torusParabolicSize w ≤ δ
  · have hy : δ ≤ torusParabolicSize w' := by linarith
    have hL : singularLocalWeight b δ w = torusParabolicSize w ^ (-b) := by
      simp [singularLocalWeight, hw, hx]
    have h1 : torusParabolicSize w' ^ (-a) ≤ δ ^ (-a) :=
      Real.rpow_le_rpow_of_nonpos hδ hy (neg_nonpos.2 ha)
    calc
      _ ≤ δ ^ (-a) * torusParabolicSize w ^ (-b) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hw.le _)
      _ = δ ^ (-a) * singularLocalWeight b δ w := by rw [hL]
      _ ≤ _ := by
        have := mul_nonneg hd2 n2
        linarith
  · by_cases hy : torusParabolicSize w' ≤ δ
    · have hx' : δ ≤ torusParabolicSize w := by linarith
      have hL : singularLocalWeight a δ w' = torusParabolicSize w' ^ (-a) := by
        simp [singularLocalWeight, hw', hy]
      have h1 : torusParabolicSize w ^ (-b) ≤ δ ^ (-b) :=
        Real.rpow_le_rpow_of_nonpos hδ hx' (neg_nonpos.2 hb)
      calc
        _ ≤ torusParabolicSize w' ^ (-a) * δ ^ (-b) :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hw'.le _)
        _ = δ ^ (-b) * singularLocalWeight a δ w' := by rw [hL]; ring
        _ ≤ _ := by
          have := mul_nonneg hd1 n1
          linarith
    · have hTx : singularTailWeight (a + b) δ w = torusParabolicSize w ^ (-(a + b)) := by
        simp [singularTailWeight, lt_of_not_ge hx]
      have hTy : singularTailWeight (a + b) δ w' = torusParabolicSize w' ^ (-(a + b)) := by
        simp [singularTailWeight, lt_of_not_ge hy]
      have h := rpow_neg_mul_le_add hw hw' ha hb
      rw [← hTx, ← hTy] at h
      have := mul_nonneg hd1 n1
      have := mul_nonneg hd2 n2
      linarith

/-- The convolution of two singularities of total order `> 5`; no support assumption. -/
theorem abs_integral_mul_singular_le_of_gt {a b : ℝ} (ha : 0 < a) (ha5 : a < 5) (hb : 0 < b)
    (hb5 : b < 5) (hab : 5 < a + b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {f g : SpaceTime → ℝ} {B₁ B₂ : ℝ}, 0 ≤ B₁ → 0 ≤ B₂ →
      (∀ w, 0 < torusParabolicSize w → |f w| ≤ B₁ * torusParabolicSize w ^ (-a)) →
      (∀ w, 0 < torusParabolicSize w → |g w| ≤ B₂ * torusParabolicSize w ^ (-b)) →
      ∀ z, 0 < torusParabolicSize z →
        ∫ w, |f (z - w)| * |g w| ≤ C * B₁ * B₂ * torusParabolicSize z ^ (5 - a - b) := by
  have hpa : 0 < a + b := by linarith
  have hab0 : 0 < a + b - 5 := by linarith
  have h5a : 0 < 5 - a := by linarith
  have h5b : 0 < 5 - b := by linarith
  have hK : 0 ≤ 80 / (5 - b) + 80 / (5 - a) + 2 * (16 * (a + b) / (a + b - 5)) := by
    have h1 : 0 ≤ 80 / (5 - b) := div_nonneg (by norm_num) h5b.le
    have h2 : 0 ≤ 80 / (5 - a) := div_nonneg (by norm_num) h5a.le
    have h3 : 0 ≤ 16 * (a + b) / (a + b - 5) := div_nonneg (by linarith) hab0.le
    linarith
  refine ⟨(80 / (5 - b) + 80 / (5 - a) + 2 * (16 * (a + b) / (a + b - 5))) /
    (8 : ℝ) ^ (5 - (a + b)), div_nonneg hK (Real.rpow_nonneg (by norm_num) _), ?_⟩
  intro f g B₁ B₂ hB₁ hB₂ hf hg z hz
  set r := torusParabolicSize z with hr
  have hδ : 0 < r / 8 := by linarith
  set δ := r / 8 with hδdef
  have iLb := integrable_singularLocalWeight hb hb5 hδ
  have iLa := integrable_singularLocalWeight ha ha5 hδ
  have iT := integrable_singularTailWeight (p := a + b) hab hδ
  have iLa' := integrable_comp_sub_left_spaceTime iLa z
  have iT' := integrable_comp_sub_left_spaceTime iT z
  let H : SpaceTime → ℝ := fun w => B₁ * B₂ * (δ ^ (-a) * singularLocalWeight b δ w +
    δ ^ (-b) * singularLocalWeight a δ (z - w) + singularTailWeight (a + b) δ w +
      singularTailWeight (a + b) δ (z - w))
  have hH : Integrable H :=
    ((((iLb.const_mul _).add (iLa'.const_mul _)).add iT).add iT').const_mul _
  have hd1 : 0 ≤ δ ^ (-a) := Real.rpow_nonneg hδ.le _
  have hd2 : 0 ≤ δ ^ (-b) := Real.rpow_nonneg hδ.le _
  have hle : ∫ w, |f (z - w)| * |g w| ≤ ∫ w, H w := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun w =>
      mul_nonneg (abs_nonneg _) (abs_nonneg _)) hH ?_
    filter_upwards [ae_torusParabolicSize_pos, ae_sub_torusParabolicSize_pos z] with w hw hw'
    have htri := torusParabolicSize_sub_le z w
    have hsplit := pointwise_split (a := a) (b := b) ha.le hb.le hδ hw hw' (by
      rw [hδdef]; linarith)
    calc
      |f (z - w)| * |g w| ≤
          (B₁ * torusParabolicSize (z - w) ^ (-a)) * (B₂ * torusParabolicSize w ^ (-b)) :=
        mul_le_mul (hf _ hw') (hg _ hw) (abs_nonneg _)
          (mul_nonneg hB₁ (Real.rpow_nonneg hw'.le _))
      _ = B₁ * B₂ * (torusParabolicSize (z - w) ^ (-a) * torusParabolicSize w ^ (-b)) := by
        ring
      _ ≤ H w := mul_le_mul_of_nonneg_left hsplit (mul_nonneg hB₁ hB₂)
  have hA : Integrable (fun w => δ ^ (-a) * singularLocalWeight b δ w) := iLb.const_mul _
  have hB : Integrable (fun w => δ ^ (-b) * singularLocalWeight a δ (z - w)) :=
    iLa'.const_mul _
  have hAB : Integrable (fun w => δ ^ (-a) * singularLocalWeight b δ w +
      δ ^ (-b) * singularLocalWeight a δ (z - w)) := hA.add hB
  have hABC : Integrable (fun w => δ ^ (-a) * singularLocalWeight b δ w +
      δ ^ (-b) * singularLocalWeight a δ (z - w) + singularTailWeight (a + b) δ w) :=
    hAB.add iT
  have hI : ∫ w, H w = B₁ * B₂ * ((δ ^ (-a) * ∫ w, singularLocalWeight b δ w) +
      (δ ^ (-b) * ∫ w, singularLocalWeight a δ w) + (∫ w, singularTailWeight (a + b) δ w) +
        ∫ w, singularTailWeight (a + b) δ w) := by
    simp only [H]
    rw [integral_const_mul, integral_add hABC iT', integral_add hAB iT, integral_add hA hB,
      integral_const_mul, integral_const_mul,
      integral_comp_sub_left_spaceTime (singularLocalWeight a δ) z,
      integral_comp_sub_left_spaceTime (singularTailWeight (a + b) δ) z]
  have e1 : δ ^ (-a) * δ ^ (5 - b) = δ ^ (5 - (a + b)) := by
    rw [← Real.rpow_add hδ]; congr 1; ring
  have e2 : δ ^ (-b) * δ ^ (5 - a) = δ ^ (5 - (a + b)) := by
    rw [← Real.rpow_add hδ]; congr 1; ring
  have bLb := integral_singularLocalWeight_le hb hb5 hδ
  have bLa := integral_singularLocalWeight_le ha ha5 hδ
  have bT := integral_singularTailWeight_le hab hδ
  have hX : δ ^ (5 - (a + b)) = r ^ (5 - a - b) / (8 : ℝ) ^ (5 - (a + b)) := by
    rw [hδdef, Real.div_rpow hz.le (by norm_num)]
    congr 2; ring
  calc
    ∫ w, |f (z - w)| * |g w| ≤ ∫ w, H w := hle
    _ = _ := hI
    _ ≤ B₁ * B₂ * (δ ^ (-a) * (80 / (5 - b) * δ ^ (5 - b)) +
          δ ^ (-b) * (80 / (5 - a) * δ ^ (5 - a)) +
          16 * (a + b) / (a + b - 5) * δ ^ (5 - (a + b)) +
          16 * (a + b) / (a + b - 5) * δ ^ (5 - (a + b))) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hB₁ hB₂)
      exact add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left bLb hd1)
        (mul_le_mul_of_nonneg_left bLa hd2)) bT) bT
    _ = B₁ * B₂ * (80 / (5 - b) * (δ ^ (-a) * δ ^ (5 - b)) +
          80 / (5 - a) * (δ ^ (-b) * δ ^ (5 - a)) +
          2 * (16 * (a + b) / (a + b - 5)) * δ ^ (5 - (a + b))) := by ring
    _ = _ := by
      rw [e1, e2, hX]
      ring

end RegularityStructures

end
