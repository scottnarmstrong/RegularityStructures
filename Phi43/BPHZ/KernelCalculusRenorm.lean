/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.KernelCalculusRenormIntegrals
public import Phi43.BPHZ.KernelCalculusRenormPointwise

/-!
# The renormalised convolution

[Hai14, Lemma 10.16 (ii)]: for `f₁` of order `-a₁` with `5 < a₁ < 6`, and `f₂` of order `-a₂`
with the increment bound `|f₂(u + h) - f₂ u| ≤ B₂ s(h) s(u)^(-a₂-1)` for `s h ≤ s u / 2`, and
`a₁ + a₂ < 10`, the renormalised convolution `∫ f₁(x) (f₂(z - x) - f₂ z) dx` is bounded by
`C B₁ B₂ s(z)^(5-a₁-a₂)` (`= s(z)^(min 0 (5-a₁-a₂))`, as `a₁ + a₂ > 5`).

The endpoint `a₁ = 5` is excluded: there the bound fails by a logarithm, `f₁ = s^(-5) 1_{s ≤ 1}`
and `f₂ = s^(-a₂)` with `a₂ > 0` giving `ρ^(-a₂) log(1/ρ)`.  No time-support hypotheses are
needed, since all majorants are integrable on `SpaceTime`.

Source: [Hai14] = arXiv:1303.5113v4, Lemma 10.16, p. 156.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

private theorem rpow_mul_rpow_div' {ρ k : ℝ} (hρ : 0 < ρ) (hk : 0 < k) (α β γ : ℝ)
    (h : α + β = γ) : ρ ^ α * (ρ / k) ^ β = k ^ (-β) * ρ ^ γ := by
  rw [Real.div_rpow hρ.le hk.le, Real.rpow_neg hk.le, ← h, Real.rpow_add hρ]
  field_simp

/-- [Hai14, Lemma 10.16 (ii)]: bound for the renormalised convolution. -/
theorem abs_integral_mul_sub_le {a₁ a₂ : ℝ} (ha₁ : 5 < a₁) (ha₁' : a₁ < 6) (ha₂ : 0 ≤ a₂)
    (ha : a₁ + a₂ < 10) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {f₁ f₂ : SpaceTime → ℝ} {B₁ B₂ : ℝ}, 0 ≤ B₁ → 0 ≤ B₂ →
      (∀ w, 0 < torusParabolicSize w → |f₁ w| ≤ B₁ * torusParabolicSize w ^ (-a₁)) →
      (∀ w, 0 < torusParabolicSize w → |f₂ w| ≤ B₂ * torusParabolicSize w ^ (-a₂)) →
      (∀ u h : SpaceTime, 0 < torusParabolicSize u →
        torusParabolicSize h ≤ torusParabolicSize u / 2 →
          |f₂ (u + h) - f₂ u| ≤ B₂ * torusParabolicSize h * torusParabolicSize u ^ (-a₂ - 1)) →
      ∀ z : SpaceTime, 0 < torusParabolicSize z →
        |∫ x, f₁ x * (f₂ (z - x) - f₂ z)| ≤
          C * B₁ * B₂ * torusParabolicSize z ^ (min 0 (5 - a₁ - a₂)) := by
  have ha₂5 : a₂ < 5 := by linarith
  obtain ⟨K₁, hK₁, h₁⟩ := integral_renorm_majorant_near (a₂ := a₂) ha₁ ha₁'
  obtain ⟨K₂, hK₂, h₂⟩ := integral_renorm_majorant_tail ha₁
  obtain ⟨K₄, hK₄, h₄⟩ := integral_renorm_majorant_far (a₁ := a₁) ha₂ ha₂5
  refine ⟨K₁ + K₂ + 8 ^ (-(-a₂)) * K₂ + K₄, by positivity, ?_⟩
  intro f₁ f₂ B₁ B₂ hB₁ hB₂ hf₁ hf₂ hinc z hz
  rw [min_eq_right (by linarith : 5 - a₁ - a₂ ≤ 0)]
  set ρ := torusParabolicSize z with hρ
  have hB : 0 ≤ B₁ * B₂ := mul_nonneg hB₁ hB₂
  have r2 : 0 ≤ ρ ^ (-a₂) := Real.rpow_nonneg hz.le _
  have r3 : 0 ≤ (ρ / 8) ^ (-a₂) := Real.rpow_nonneg (by positivity) _
  obtain ⟨i₁, e₁⟩ := h₁ hz hB
  obtain ⟨i₂, e₂⟩ := h₂ hz (mul_nonneg hB r2)
  obtain ⟨i₃, e₃⟩ := h₂ hz (mul_nonneg hB r3)
  obtain ⟨i₄, e₄⟩ := h₄ z hz hB
  have i12 : Integrable (fun x => B₁ * B₂ * (2 * ρ ^ (-a₂ - 1)) *
          singularLocalWeight (a₁ - 1) (ρ / 4) x +
        B₁ * B₂ * ρ ^ (-a₂) * singularTailWeight a₁ (ρ / 4) x) := i₁.add i₂
  have i123 : Integrable (fun x => B₁ * B₂ * (2 * ρ ^ (-a₂ - 1)) *
          singularLocalWeight (a₁ - 1) (ρ / 4) x +
        B₁ * B₂ * ρ ^ (-a₂) * singularTailWeight a₁ (ρ / 4) x +
        B₁ * B₂ * (ρ / 8) ^ (-a₂) * singularTailWeight a₁ (ρ / 4) x) := i12.add i₃
  have hG : Integrable (fun x => B₁ * B₂ * (2 * ρ ^ (-a₂ - 1)) *
          singularLocalWeight (a₁ - 1) (ρ / 4) x +
        B₁ * B₂ * ρ ^ (-a₂) * singularTailWeight a₁ (ρ / 4) x +
        B₁ * B₂ * (ρ / 8) ^ (-a₂) * singularTailWeight a₁ (ρ / 4) x +
        B₁ * B₂ * ((ρ / 4) ^ (-a₁) * (ρ / 8) ^ ((5 - a₂) / 2)) *
          singularLocalWeight ((5 + a₂) / 2) (ρ / 8) (z - x)) :=
    i123.add i₄
  have hae : ∀ᵐ x : SpaceTime ∂volume, ‖f₁ x * (f₂ (z - x) - f₂ z)‖ ≤
      B₁ * B₂ * (2 * ρ ^ (-a₂ - 1)) * singularLocalWeight (a₁ - 1) (ρ / 4) x +
        B₁ * B₂ * ρ ^ (-a₂) * singularTailWeight a₁ (ρ / 4) x +
        B₁ * B₂ * (ρ / 8) ^ (-a₂) * singularTailWeight a₁ (ρ / 4) x +
        B₁ * B₂ * ((ρ / 4) ^ (-a₁) * (ρ / 8) ^ ((5 - a₂) / 2)) *
          singularLocalWeight ((5 + a₂) / 2) (ρ / 8) (z - x) := by
    filter_upwards [ae_torusParabolicSize_pos_spaceTime, ae_torusParabolicSize_sub_pos z]
      with x hx hzx
    rw [Real.norm_eq_abs]
    exact abs_mul_sub_le_majorant ha₁ ha₂ ha₂5 hB₁ hB₂ hf₁ hf₂ hinc hz hx hzx
  have hnorm := norm_integral_le_of_norm_le hG hae
  rw [Real.norm_eq_abs] at hnorm
  have hsum : ∫ x, (B₁ * B₂ * (2 * ρ ^ (-a₂ - 1)) * singularLocalWeight (a₁ - 1) (ρ / 4) x +
        B₁ * B₂ * ρ ^ (-a₂) * singularTailWeight a₁ (ρ / 4) x +
        B₁ * B₂ * (ρ / 8) ^ (-a₂) * singularTailWeight a₁ (ρ / 4) x +
        B₁ * B₂ * ((ρ / 4) ^ (-a₁) * (ρ / 8) ^ ((5 - a₂) / 2)) *
          singularLocalWeight ((5 + a₂) / 2) (ρ / 8) (z - x)) =
      (∫ x, B₁ * B₂ * (2 * ρ ^ (-a₂ - 1)) * singularLocalWeight (a₁ - 1) (ρ / 4) x) +
      (∫ x, B₁ * B₂ * ρ ^ (-a₂) * singularTailWeight a₁ (ρ / 4) x) +
      (∫ x, B₁ * B₂ * (ρ / 8) ^ (-a₂) * singularTailWeight a₁ (ρ / 4) x) +
      ∫ x, B₁ * B₂ * ((ρ / 4) ^ (-a₁) * (ρ / 8) ^ ((5 - a₂) / 2)) *
          singularLocalWeight ((5 + a₂) / 2) (ρ / 8) (z - x) := by
    rw [integral_add i123 i₄, integral_add i12 i₃, integral_add i₁ i₂]
  have k2 : ρ ^ (-a₂) * ρ ^ (5 - a₁) = ρ ^ (5 - a₁ - a₂) := by
    rw [← Real.rpow_add hz]; ring_nf
  have k3 := rpow_mul_rpow_div' hz (by norm_num : (0 : ℝ) < 8) (5 - a₁) (-a₂) (5 - a₁ - a₂)
    (by ring)
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
