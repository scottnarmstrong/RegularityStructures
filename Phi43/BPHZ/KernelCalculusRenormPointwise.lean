/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.KernelCalculusBasic

/-!
# Pointwise bound for the renormalised convolution

The integrand `f₁(x) (f₂(z - x) - f₂(z))` of [Hai14, Lemma 10.16 (ii)] is bounded, for
`s(z) = ρ`, by the sum of four integrable majorants: the near zone `s(x) ≤ ρ/4` (increment
bound), the tail of `f₁` against `f₂(z)`, the tail of `f₁` against `f₂(z - x)` away from the
singularity of `f₂`, and the neighbourhood of that singularity.

Source: [Hai14] = arXiv:1303.5113v4, Lemma 10.16, p. 156.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

private theorem rpow_neg_mul_self_eq {x a : ℝ} (hx : 0 < x) :
    x ^ (-a) * x = x ^ (-(a - 1)) := by
  have := Real.rpow_add hx (-a) 1
  rw [Real.rpow_one] at this
  rw [← this]; ring_nf

/-- Pointwise bound for the integrand of the renormalised convolution. -/
theorem abs_mul_sub_le_majorant {a₁ a₂ B₁ B₂ : ℝ} {f₁ f₂ : SpaceTime → ℝ} (ha₁ : 5 < a₁)
    (ha₂ : 0 ≤ a₂) (ha₂5 : a₂ < 5) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hf₁ : ∀ w, 0 < torusParabolicSize w → |f₁ w| ≤ B₁ * torusParabolicSize w ^ (-a₁))
    (hf₂ : ∀ w, 0 < torusParabolicSize w → |f₂ w| ≤ B₂ * torusParabolicSize w ^ (-a₂))
    (hinc : ∀ u h : SpaceTime, 0 < torusParabolicSize u →
      torusParabolicSize h ≤ torusParabolicSize u / 2 →
        |f₂ (u + h) - f₂ u| ≤ B₂ * torusParabolicSize h * torusParabolicSize u ^ (-a₂ - 1))
    {z : SpaceTime} (hz : 0 < torusParabolicSize z) {x : SpaceTime}
    (hx : 0 < torusParabolicSize x) (hzx : 0 < torusParabolicSize (z - x)) :
    |f₁ x * (f₂ (z - x) - f₂ z)| ≤
      B₁ * B₂ * (2 * torusParabolicSize z ^ (-a₂ - 1)) *
          singularLocalWeight (a₁ - 1) (torusParabolicSize z / 4) x +
        B₁ * B₂ * torusParabolicSize z ^ (-a₂) *
          singularTailWeight a₁ (torusParabolicSize z / 4) x +
        B₁ * B₂ * (torusParabolicSize z / 8) ^ (-a₂) *
          singularTailWeight a₁ (torusParabolicSize z / 4) x +
        B₁ * B₂ * ((torusParabolicSize z / 4) ^ (-a₁) *
          (torusParabolicSize z / 8) ^ ((5 - a₂) / 2)) *
          singularLocalWeight ((5 + a₂) / 2) (torusParabolicSize z / 8) (z - x) := by
  set ρ := torusParabolicSize z with hρ
  have hB12 : 0 ≤ B₁ * B₂ := mul_nonneg hB₁ hB₂
  have n1 := singularLocalWeight_nonneg (a₁ - 1) (ρ / 4) x
  have n2 := singularTailWeight_nonneg a₁ (ρ / 4) x
  have n4 := singularLocalWeight_nonneg ((5 + a₂) / 2) (ρ / 8) (z - x)
  have r1 : 0 ≤ ρ ^ (-a₂ - 1) := Real.rpow_nonneg hz.le _
  have r2 : 0 ≤ ρ ^ (-a₂) := Real.rpow_nonneg hz.le _
  have r3 : 0 ≤ (ρ / 8) ^ (-a₂) := Real.rpow_nonneg (by positivity) _
  have r4 : 0 ≤ (ρ / 4) ^ (-a₁) * (ρ / 8) ^ ((5 - a₂) / 2) :=
    mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _)
  have g1 : 0 ≤ B₁ * B₂ * (2 * ρ ^ (-a₂ - 1)) * singularLocalWeight (a₁ - 1) (ρ / 4) x :=
    mul_nonneg (mul_nonneg hB12 (by linarith)) n1
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
  · -- near zone: increment bound
    have hneg := torusParabolicSize_neg_le_two_mul x
    have h1 := hinc z (-x) hz (by linarith)
    rw [← sub_eq_add_neg] at h1
    have hloc : singularLocalWeight (a₁ - 1) (ρ / 4) x =
        torusParabolicSize x ^ (-(a₁ - 1)) := by
      simp [singularLocalWeight, hx, hnear]
    have e1 : |f₁ x| * |f₂ (z - x) - f₂ z| ≤
        B₁ * B₂ * (2 * ρ ^ (-a₂ - 1)) * singularLocalWeight (a₁ - 1) (ρ / 4) x := by
      calc
        |f₁ x| * |f₂ (z - x) - f₂ z| ≤
            (B₁ * torusParabolicSize x ^ (-a₁)) *
              (B₂ * (2 * torusParabolicSize x) * ρ ^ (-a₂ - 1)) := by
          apply mul_le_mul hf1 _ (abs_nonneg _) (mul_nonneg hB₁ hx0)
          refine h1.trans ?_
          apply mul_le_mul_of_nonneg_right _ r1
          exact mul_le_mul_of_nonneg_left hneg hB₂
        _ = B₁ * B₂ * (2 * ρ ^ (-a₂ - 1)) *
            (torusParabolicSize x ^ (-a₁) * torusParabolicSize x) := by ring
        _ = _ := by rw [hloc, rpow_neg_mul_self_eq hx]
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

end RegularityStructures

end
