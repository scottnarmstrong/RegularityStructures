/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.KernelCalculusRenorm

/-!
# The renormalised convolution with Hölder increments

A variant of [Hai14, Lemma 10.16 (ii)] (`abs_integral_mul_sub_le`) in which the increment bound of
`f₂` is Hölder of exponent `lam ∈ (0, 1]`:
`|f₂(u + h) - f₂ u| ≤ B₂ s(h)^lam s(u)^(-a₂-lam)` for `s h ≤ s u / 2`.  If `f₁` has order `-a₁` with
`5 < a₁ < 5 + lam` and `f₂` order `-a₂`, then
`|∫ f₁(x) (f₂(z - x) - f₂ z) dx| ≤ C B₁ B₂ s(z)^(5-a₁-a₂)`.  This is needed for the difference of
renormalised convolutions, where `f₂` is a difference of kernels whose Hölder increments gain a
power of the distance between the scales by interpolation.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

private theorem rpow_mul_rpow_div_holder {ρ k : ℝ} (hρ : 0 < ρ) (hk : 0 < k) (α β γ : ℝ)
    (h : α + β = γ) : ρ ^ α * (ρ / k) ^ β = k ^ (-β) * ρ ^ γ := by
  rw [Real.div_rpow hρ.le hk.le, Real.rpow_neg hk.le, ← h, Real.rpow_add hρ]
  field_simp

private theorem rpow_neg_mul_rpow_self_eq {x a lam : ℝ} (hx : 0 < x) :
    x ^ (-a) * x ^ lam = x ^ (-(a - lam)) := by
  rw [← Real.rpow_add hx]; ring_nf

/-- The near-zone majorant of the renormalised convolution with Hölder increments. -/
theorem integral_renorm_majorant_near_holder {a₁ a₂ lam : ℝ} (hlam1 : lam ≤ 1)
    (ha₁ : 5 < a₁) (ha₁' : a₁ - lam < 5) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ρ B : ℝ}, 0 < ρ → 0 ≤ B →
      Integrable (fun x => B * (2 ^ lam * ρ ^ (-a₂ - lam)) *
        singularLocalWeight (a₁ - lam) (ρ / 4) x) ∧
      ∫ x, B * (2 ^ lam * ρ ^ (-a₂ - lam)) * singularLocalWeight (a₁ - lam) (ρ / 4) x ≤
        B * K * ρ ^ (5 - a₁ - a₂) := by
  have hp : 0 < a₁ - lam := by linarith
  have h5 : 0 < 5 - (a₁ - lam) := by linarith
  refine ⟨2 ^ lam * (80 / (5 - (a₁ - lam)) * 4 ^ (-(5 - (a₁ - lam)))), by positivity, ?_⟩
  intro ρ B hρ hB
  have iL := integrable_singularLocalWeight hp ha₁' (by positivity : 0 < ρ / 4)
  refine ⟨iL.const_mul _, ?_⟩
  rw [integral_const_mul]
  have hb := integral_singularLocalWeight_le hp ha₁' (by positivity : 0 < ρ / 4)
  have hc : 0 ≤ B * (2 ^ lam * ρ ^ (-a₂ - lam)) := by
    have := Real.rpow_nonneg hρ.le (-a₂ - lam)
    have h2 : (0 : ℝ) ≤ 2 ^ lam := Real.rpow_nonneg (by norm_num) _
    positivity
  have key := rpow_mul_rpow_div_holder hρ (by norm_num : (0 : ℝ) < 4) (-a₂ - lam)
    (5 - (a₁ - lam)) (5 - a₁ - a₂) (by ring)
  calc
    B * (2 ^ lam * ρ ^ (-a₂ - lam)) * ∫ x, singularLocalWeight (a₁ - lam) (ρ / 4) x ≤
        B * (2 ^ lam * ρ ^ (-a₂ - lam)) * (80 / (5 - (a₁ - lam)) * (ρ / 4) ^ (5 - (a₁ - lam))) :=
      mul_le_mul_of_nonneg_left hb hc
    _ = B * 2 ^ lam * (80 / (5 - (a₁ - lam))) *
        (ρ ^ (-a₂ - lam) * (ρ / 4) ^ (5 - (a₁ - lam))) := by ring
    _ = _ := by rw [key]; ring

/-- Pointwise bound for the integrand of the renormalised convolution with Hölder increments. -/
theorem abs_mul_sub_le_majorant_holder {a₁ a₂ lam B₁ B₂ : ℝ} {f₁ f₂ : SpaceTime → ℝ}
    (hlam : 0 < lam) (ha₁ : 5 < a₁) (ha₂ : 0 ≤ a₂) (ha₂5 : a₂ < 5)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hf₁ : ∀ w, 0 < torusParabolicSize w → |f₁ w| ≤ B₁ * torusParabolicSize w ^ (-a₁))
    (hf₂ : ∀ w, 0 < torusParabolicSize w → |f₂ w| ≤ B₂ * torusParabolicSize w ^ (-a₂))
    (hinc : ∀ u h : SpaceTime, 0 < torusParabolicSize u →
      torusParabolicSize h ≤ torusParabolicSize u / 2 →
        |f₂ (u + h) - f₂ u| ≤ B₂ * torusParabolicSize h ^ lam * torusParabolicSize u ^ (-a₂ - lam))
    {z : SpaceTime} (hz : 0 < torusParabolicSize z) {x : SpaceTime}
    (hx : 0 < torusParabolicSize x) (hzx : 0 < torusParabolicSize (z - x)) :
    |f₁ x * (f₂ (z - x) - f₂ z)| ≤
      B₁ * B₂ * (2 ^ lam * torusParabolicSize z ^ (-a₂ - lam)) *
          singularLocalWeight (a₁ - lam) (torusParabolicSize z / 4) x +
        B₁ * B₂ * torusParabolicSize z ^ (-a₂) *
          singularTailWeight a₁ (torusParabolicSize z / 4) x +
        B₁ * B₂ * (torusParabolicSize z / 8) ^ (-a₂) *
          singularTailWeight a₁ (torusParabolicSize z / 4) x +
        B₁ * B₂ * ((torusParabolicSize z / 4) ^ (-a₁) *
          (torusParabolicSize z / 8) ^ ((5 - a₂) / 2)) *
          singularLocalWeight ((5 + a₂) / 2) (torusParabolicSize z / 8) (z - x) := by
  set ρ := torusParabolicSize z with hρ
  have hB12 : 0 ≤ B₁ * B₂ := mul_nonneg hB₁ hB₂
  have n1 := singularLocalWeight_nonneg (a₁ - lam) (ρ / 4) x
  have n2 := singularTailWeight_nonneg a₁ (ρ / 4) x
  have n4 := singularLocalWeight_nonneg ((5 + a₂) / 2) (ρ / 8) (z - x)
  have p2 : (0 : ℝ) ≤ 2 ^ lam := Real.rpow_nonneg (by norm_num) _
  have r1 : 0 ≤ ρ ^ (-a₂ - lam) := Real.rpow_nonneg hz.le _
  have r2 : 0 ≤ ρ ^ (-a₂) := Real.rpow_nonneg hz.le _
  have r3 : 0 ≤ (ρ / 8) ^ (-a₂) := Real.rpow_nonneg (by positivity) _
  have r4 : 0 ≤ (ρ / 4) ^ (-a₁) * (ρ / 8) ^ ((5 - a₂) / 2) :=
    mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _)
  have g1 : 0 ≤ B₁ * B₂ * (2 ^ lam * ρ ^ (-a₂ - lam)) *
      singularLocalWeight (a₁ - lam) (ρ / 4) x :=
    mul_nonneg (mul_nonneg hB12 (mul_nonneg p2 r1)) n1
  have g2 : 0 ≤ B₁ * B₂ * ρ ^ (-a₂) * singularTailWeight a₁ (ρ / 4) x :=
    mul_nonneg (mul_nonneg hB12 r2) n2
  have g3 : 0 ≤ B₁ * B₂ * (ρ / 8) ^ (-a₂) * singularTailWeight a₁ (ρ / 4) x :=
    mul_nonneg (mul_nonneg hB12 r3) n2
  have g4 : 0 ≤ B₁ * B₂ * ((ρ / 4) ^ (-a₁) * (ρ / 8) ^ ((5 - a₂) / 2)) *
      singularLocalWeight ((5 + a₂) / 2) (ρ / 8) (z - x) :=
    mul_nonneg (mul_nonneg hB12 r4) n4
  rw [abs_mul]
  have hf1 := hf₁ x hx
  have hx0 : 0 ≤ torusParabolicSize x ^ (-a₁) := Real.rpow_nonneg hx.le _
  rcases le_or_gt (torusParabolicSize x) (ρ / 4) with hnear | hfar
  · -- near zone: Hölder increment bound
    have hneg := torusParabolicSize_neg_le_two_mul x
    have h1 := hinc z (-x) hz (by linarith)
    rw [← sub_eq_add_neg] at h1
    have hloc : singularLocalWeight (a₁ - lam) (ρ / 4) x =
        torusParabolicSize x ^ (-(a₁ - lam)) := by
      simp [singularLocalWeight, hx, hnear]
    have h2lam : torusParabolicSize (-x) ^ lam ≤ (2 * torusParabolicSize x) ^ lam :=
      Real.rpow_le_rpow (torusParabolicSize_nonneg _) hneg hlam.le
    have h2m : (2 * torusParabolicSize x) ^ lam = 2 ^ lam * torusParabolicSize x ^ lam :=
      Real.mul_rpow (by norm_num) hx.le
    have e1 : |f₁ x| * |f₂ (z - x) - f₂ z| ≤
        B₁ * B₂ * (2 ^ lam * ρ ^ (-a₂ - lam)) * singularLocalWeight (a₁ - lam) (ρ / 4) x := by
      calc
        |f₁ x| * |f₂ (z - x) - f₂ z| ≤
            (B₁ * torusParabolicSize x ^ (-a₁)) *
              (B₂ * (2 ^ lam * torusParabolicSize x ^ lam) * ρ ^ (-a₂ - lam)) := by
          apply mul_le_mul hf1 _ (abs_nonneg _) (mul_nonneg hB₁ hx0)
          refine h1.trans ?_
          apply mul_le_mul_of_nonneg_right _ r1
          exact mul_le_mul_of_nonneg_left (h2lam.trans h2m.le) hB₂
        _ = B₁ * B₂ * (2 ^ lam * ρ ^ (-a₂ - lam)) *
            (torusParabolicSize x ^ (-a₁) * torusParabolicSize x ^ lam) := by ring
        _ = _ := by rw [hloc, rpow_neg_mul_rpow_self_eq hx]
    linarith
  · -- far zone
    have htail : singularTailWeight a₁ (ρ / 4) x = torusParabolicSize x ^ (-a₁) := by
      simp [singularTailWeight, hfar]
    have hb : |f₁ x| * |f₂ z| ≤ B₁ * B₂ * ρ ^ (-a₂) * singularTailWeight a₁ (ρ / 4) x := by
      calc
        |f₁ x| * |f₂ z| ≤ (B₁ * torusParabolicSize x ^ (-a₁)) * (B₂ * ρ ^ (-a₂)) :=
          mul_le_mul hf1 (hf₂ z hz) (abs_nonneg _) (mul_nonneg hB₁ hx0)
        _ = _ := by rw [htail]; ring
    have hsplit : |f₁ x| * |f₂ (z - x) - f₂ z| ≤
        |f₁ x| * |f₂ (z - x)| + |f₁ x| * |f₂ z| := by
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg _)
    have ha : |f₁ x| * |f₂ (z - x)| ≤
        B₁ * B₂ * (ρ / 8) ^ (-a₂) * singularTailWeight a₁ (ρ / 4) x +
        B₁ * B₂ * ((ρ / 4) ^ (-a₁) * (ρ / 8) ^ ((5 - a₂) / 2)) *
          singularLocalWeight ((5 + a₂) / 2) (ρ / 8) (z - x) := by
      rcases le_or_gt (ρ / 8) (torusParabolicSize (z - x)) with hfz | hnz
      · have h2 : torusParabolicSize (z - x) ^ (-a₂) ≤ (ρ / 8) ^ (-a₂) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hfz (by linarith)
        have : |f₁ x| * |f₂ (z - x)| ≤ B₁ * B₂ * (ρ / 8) ^ (-a₂) *
            singularTailWeight a₁ (ρ / 4) x := by
          calc
            |f₁ x| * |f₂ (z - x)| ≤ (B₁ * torusParabolicSize x ^ (-a₁)) *
                (B₂ * torusParabolicSize (z - x) ^ (-a₂)) :=
              mul_le_mul hf1 (hf₂ _ hzx) (abs_nonneg _) (mul_nonneg hB₁ hx0)
            _ ≤ (B₁ * torusParabolicSize x ^ (-a₁)) * (B₂ * (ρ / 8) ^ (-a₂)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hB₂)
                (mul_nonneg hB₁ hx0)
            _ = _ := by rw [htail]; ring
        linarith
      · have hε : 0 ≤ (5 - a₂) / 2 := by linarith
        have hloc : singularLocalWeight ((5 + a₂) / 2) (ρ / 8) (z - x) =
            torusParabolicSize (z - x) ^ (-((5 + a₂) / 2)) := by
          simp [singularLocalWeight, hzx, hnz.le]
        have e1 : |f₁ x| ≤ B₁ * (ρ / 4) ^ (-a₁) := by
          refine hf1.trans (mul_le_mul_of_nonneg_left ?_ hB₁)
          exact Real.rpow_le_rpow_of_nonpos (by positivity) hfar.le (by linarith)
        have e2 : |f₂ (z - x)| ≤ B₂ * ((ρ / 8) ^ ((5 - a₂) / 2) *
            torusParabolicSize (z - x) ^ (-((5 + a₂) / 2))) := by
          refine (hf₂ _ hzx).trans (mul_le_mul_of_nonneg_left ?_ hB₂)
          have hsplit' : torusParabolicSize (z - x) ^ (-a₂) =
              torusParabolicSize (z - x) ^ ((5 - a₂) / 2) *
                torusParabolicSize (z - x) ^ (-((5 + a₂) / 2)) := by
            rw [← Real.rpow_add hzx]; ring_nf
          rw [hsplit']
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hzx.le _)
          exact Real.rpow_le_rpow hzx.le hnz.le hε
        have : |f₁ x| * |f₂ (z - x)| ≤ B₁ * B₂ * ((ρ / 4) ^ (-a₁) *
            (ρ / 8) ^ ((5 - a₂) / 2)) *
              singularLocalWeight ((5 + a₂) / 2) (ρ / 8) (z - x) := by
          rw [hloc]
          calc
            |f₁ x| * |f₂ (z - x)| ≤ (B₁ * (ρ / 4) ^ (-a₁)) * (B₂ * ((ρ / 8) ^ ((5 - a₂) / 2) *
                torusParabolicSize (z - x) ^ (-((5 + a₂) / 2)))) :=
              mul_le_mul e1 e2 (abs_nonneg _) (mul_nonneg hB₁ (Real.rpow_nonneg (by positivity) _))
            _ = _ := by ring
        linarith
    linarith

/-- **The renormalised convolution with Hölder increments** (variant of [Hai14, Lemma 10.16 (ii)]). -/
theorem abs_integral_mul_sub_le_holder {a₁ a₂ lam : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (ha₁ : 5 < a₁) (ha₁lam : a₁ - lam < 5) (ha₂ : 0 ≤ a₂) (ha : a₁ + a₂ < 10) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {f₁ f₂ : SpaceTime → ℝ} {B₁ B₂ : ℝ}, 0 ≤ B₁ → 0 ≤ B₂ →
      (∀ w, 0 < torusParabolicSize w → |f₁ w| ≤ B₁ * torusParabolicSize w ^ (-a₁)) →
      (∀ w, 0 < torusParabolicSize w → |f₂ w| ≤ B₂ * torusParabolicSize w ^ (-a₂)) →
      (∀ u h : SpaceTime, 0 < torusParabolicSize u →
        torusParabolicSize h ≤ torusParabolicSize u / 2 →
          |f₂ (u + h) - f₂ u| ≤
            B₂ * torusParabolicSize h ^ lam * torusParabolicSize u ^ (-a₂ - lam)) →
      ∀ z : SpaceTime, 0 < torusParabolicSize z →
        |∫ x, f₁ x * (f₂ (z - x) - f₂ z)| ≤
          C * B₁ * B₂ * torusParabolicSize z ^ (5 - a₁ - a₂) := by
  have ha₂5 : a₂ < 5 := by linarith
  obtain ⟨K₁, hK₁, h₁⟩ := integral_renorm_majorant_near_holder (a₂ := a₂) hlam1 ha₁ ha₁lam
  obtain ⟨K₂, hK₂, h₂⟩ := integral_renorm_majorant_tail ha₁
  obtain ⟨K₄, hK₄, h₄⟩ := integral_renorm_majorant_far (a₁ := a₁) ha₂ ha₂5
  refine ⟨K₁ + K₂ + 8 ^ (-(-a₂)) * K₂ + K₄, by positivity, ?_⟩
  intro f₁ f₂ B₁ B₂ hB₁ hB₂ hf₁ hf₂ hinc z hz
  set ρ := torusParabolicSize z with hρ
  have hB : 0 ≤ B₁ * B₂ := mul_nonneg hB₁ hB₂
  have r2 : 0 ≤ ρ ^ (-a₂) := Real.rpow_nonneg hz.le _
  have r3 : 0 ≤ (ρ / 8) ^ (-a₂) := Real.rpow_nonneg (by positivity) _
  obtain ⟨i₁, e₁⟩ := h₁ hz hB
  obtain ⟨i₂, e₂⟩ := h₂ hz (mul_nonneg hB r2)
  obtain ⟨i₃, e₃⟩ := h₂ hz (mul_nonneg hB r3)
  obtain ⟨i₄, e₄⟩ := h₄ z hz hB
  have i12 : Integrable (fun x => B₁ * B₂ * (2 ^ lam * ρ ^ (-a₂ - lam)) *
          singularLocalWeight (a₁ - lam) (ρ / 4) x +
        B₁ * B₂ * ρ ^ (-a₂) * singularTailWeight a₁ (ρ / 4) x) := i₁.add i₂
  have i123 : Integrable (fun x => B₁ * B₂ * (2 ^ lam * ρ ^ (-a₂ - lam)) *
          singularLocalWeight (a₁ - lam) (ρ / 4) x +
        B₁ * B₂ * ρ ^ (-a₂) * singularTailWeight a₁ (ρ / 4) x +
        B₁ * B₂ * (ρ / 8) ^ (-a₂) * singularTailWeight a₁ (ρ / 4) x) := i12.add i₃
  have hG : Integrable (fun x => B₁ * B₂ * (2 ^ lam * ρ ^ (-a₂ - lam)) *
          singularLocalWeight (a₁ - lam) (ρ / 4) x +
        B₁ * B₂ * ρ ^ (-a₂) * singularTailWeight a₁ (ρ / 4) x +
        B₁ * B₂ * (ρ / 8) ^ (-a₂) * singularTailWeight a₁ (ρ / 4) x +
        B₁ * B₂ * ((ρ / 4) ^ (-a₁) * (ρ / 8) ^ ((5 - a₂) / 2)) *
          singularLocalWeight ((5 + a₂) / 2) (ρ / 8) (z - x)) :=
    i123.add i₄
  have hae : ∀ᵐ x : SpaceTime ∂volume, ‖f₁ x * (f₂ (z - x) - f₂ z)‖ ≤
      B₁ * B₂ * (2 ^ lam * ρ ^ (-a₂ - lam)) * singularLocalWeight (a₁ - lam) (ρ / 4) x +
        B₁ * B₂ * ρ ^ (-a₂) * singularTailWeight a₁ (ρ / 4) x +
        B₁ * B₂ * (ρ / 8) ^ (-a₂) * singularTailWeight a₁ (ρ / 4) x +
        B₁ * B₂ * ((ρ / 4) ^ (-a₁) * (ρ / 8) ^ ((5 - a₂) / 2)) *
          singularLocalWeight ((5 + a₂) / 2) (ρ / 8) (z - x) := by
    filter_upwards [ae_torusParabolicSize_pos_spaceTime, ae_torusParabolicSize_sub_pos z]
      with x hx hzx
    rw [Real.norm_eq_abs]
    exact abs_mul_sub_le_majorant_holder hlam ha₁ ha₂ ha₂5 hB₁ hB₂ hf₁ hf₂ hinc hz hx hzx
  have hnorm := norm_integral_le_of_norm_le hG hae
  rw [Real.norm_eq_abs] at hnorm
  have hsum : ∫ x, (B₁ * B₂ * (2 ^ lam * ρ ^ (-a₂ - lam)) *
          singularLocalWeight (a₁ - lam) (ρ / 4) x +
        B₁ * B₂ * ρ ^ (-a₂) * singularTailWeight a₁ (ρ / 4) x +
        B₁ * B₂ * (ρ / 8) ^ (-a₂) * singularTailWeight a₁ (ρ / 4) x +
        B₁ * B₂ * ((ρ / 4) ^ (-a₁) * (ρ / 8) ^ ((5 - a₂) / 2)) *
          singularLocalWeight ((5 + a₂) / 2) (ρ / 8) (z - x)) =
      (∫ x, B₁ * B₂ * (2 ^ lam * ρ ^ (-a₂ - lam)) * singularLocalWeight (a₁ - lam) (ρ / 4) x) +
      (∫ x, B₁ * B₂ * ρ ^ (-a₂) * singularTailWeight a₁ (ρ / 4) x) +
      (∫ x, B₁ * B₂ * (ρ / 8) ^ (-a₂) * singularTailWeight a₁ (ρ / 4) x) +
      ∫ x, B₁ * B₂ * ((ρ / 4) ^ (-a₁) * (ρ / 8) ^ ((5 - a₂) / 2)) *
          singularLocalWeight ((5 + a₂) / 2) (ρ / 8) (z - x) := by
    rw [integral_add i123 i₄, integral_add i12 i₃, integral_add i₁ i₂]
  have k2 : ρ ^ (-a₂) * ρ ^ (5 - a₁) = ρ ^ (5 - a₁ - a₂) := by
    rw [← Real.rpow_add hz]; ring_nf
  have k3 := rpow_mul_rpow_div_holder hz (by norm_num : (0 : ℝ) < 8) (5 - a₁) (-a₂)
    (5 - a₁ - a₂) (by ring)
  have hE : B₁ * B₂ * ρ ^ (-a₂) * K₂ * ρ ^ (5 - a₁) = B₁ * B₂ * K₂ * ρ ^ (5 - a₁ - a₂) := by
    linear_combination (B₁ * B₂ * K₂) * k2
  have hE3 : B₁ * B₂ * (ρ / 8) ^ (-a₂) * K₂ * ρ ^ (5 - a₁) =
      B₁ * B₂ * (8 ^ (-(-a₂)) * K₂) * ρ ^ (5 - a₁ - a₂) := by
    linear_combination (B₁ * B₂ * K₂) * k3
  rw [hsum] at hnorm
  calc
    |∫ x, f₁ x * (f₂ (z - x) - f₂ z)| ≤ _ := hnorm
    _ ≤ B₁ * B₂ * K₁ * ρ ^ (5 - a₁ - a₂) + B₁ * B₂ * ρ ^ (-a₂) * K₂ * ρ ^ (5 - a₁) +
        B₁ * B₂ * (ρ / 8) ^ (-a₂) * K₂ * ρ ^ (5 - a₁) +
        B₁ * B₂ * K₄ * ρ ^ (5 - a₁ - a₂) := add_le_add (add_le_add (add_le_add e₁ e₂) e₃) e₄
    _ = _ := by rw [hE, hE3]; ring

end RegularityStructures

end
