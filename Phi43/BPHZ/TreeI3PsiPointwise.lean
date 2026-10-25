/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.KernelCalculusIncrement
public import Phi43.BPHZ.TreeI3PsiSlab

/-!
# Pointwise bounds for the recentred kernel and the covariance

For abstract functions `K` (order `-3` with increments of order `-4`, time support `|t| ≤ 1`)
and `Q` (order `-1`, time support `|t| ≤ 2`) we bound, in terms of centred powers
`singularPow`,

* the recentred kernel `δK(z, w) = K(z - w) - K(-w)`, with and without a Hölder gain
  `s(z)^θ`;
* the covariance at a flipped argument, `|Q(w - u)| ≤ 2 B s(u - w)⁻¹`;
* the square and the cube of the covariance, the square with a loss `δ` of the exponent.

Source: [Hai14] = arXiv:1303.5113v4, Lemma 10.18 and p. 167--168.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

/-- Trivial bound for the recentred kernel. -/
theorem abs_dK_le {K : SpaceTime → ℝ} {B : ℝ}
    (hK : ∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ)))
    {z w : SpaceTime} (hz : 0 < torusParabolicSize (z - w))
    (h0 : 0 < torusParabolicSize (0 - w)) :
    |K (z - w) - K (-w)| ≤ B * (singularPow 3 z w + singularPow 3 0 w) := by
  have h1 := hK _ hz
  have h2 := hK (0 - w) h0
  rw [zero_sub] at h2
  have e : singularPow 3 0 w = torusParabolicSize (-w) ^ (-(3 : ℝ)) := by
    simp [singularPow]
  rw [e]
  have e' : singularPow 3 z w = torusParabolicSize (z - w) ^ (-(3 : ℝ)) := by
    simp [singularPow]
  rw [e']
  calc |K (z - w) - K (-w)| ≤ |K (z - w)| + |K (-w)| := abs_sub _ _
    _ ≤ _ := by linarith

/-- Hölder-gain bound for the recentred kernel, from the increment bound of order `-4`. -/
theorem abs_dK_le_holder {K : SpaceTime → ℝ} {B θ : ℝ} (hB : 0 ≤ B) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hK : ∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ)))
    (hinc : ∀ u h : SpaceTime, 0 < torusParabolicSize u →
      torusParabolicSize h ≤ torusParabolicSize u / 2 →
        |K (u + h) - K u| ≤ B * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ)))
    {z w : SpaceTime} (hz : 0 < torusParabolicSize (z - w))
    (h0 : 0 < torusParabolicSize (0 - w)) :
    |K (z - w) - K (-w)| ≤ 12 * B * torusParabolicSize z ^ θ *
      (singularPow (3 + θ) z w + singularPow (3 + θ) 0 w) := by
  have hinc' : ∀ u h : SpaceTime, 0 < torusParabolicSize u →
      torusParabolicSize h ≤ torusParabolicSize u / 2 →
        |K (u + h) - K u| ≤ B * torusParabolicSize h * torusParabolicSize u ^ (-(3 : ℝ) - 1) := by
    intro u h hu hh
    have := hinc u h hu hh
    have e : (-(3 : ℝ) - 1) = -(4 : ℝ) := by norm_num
    rw [e]; exact this
  have h0' : 0 < torusParabolicSize (-w) := by simpa using h0
  have := abs_sub_le_of_increment (f := K) (a := 3) hB hθ0 hθ1 hK hinc' hz h0'
  have e1 : z - w - -w = z := by abel
  rw [e1] at this
  have e2 : (-(3 : ℝ) - θ) = -(3 + θ) := by ring
  rw [e2] at this
  simpa [singularPow] using this

/-- The covariance at a flipped argument. -/
theorem abs_Q_flip_le {Q : SpaceTime → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hQ : ∀ x, 0 < torusParabolicSize x → |Q x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ)))
    {u w : SpaceTime} (h : 0 < torusParabolicSize (u - w)) :
    |Q (w - u)| ≤ 2 * B * singularPow 1 u w := by
  have hneg := torusParabolicSize_neg_le_two_mul (w - u)
  rw [neg_sub] at hneg
  set x := torusParabolicSize (w - u)
  set y := torusParabolicSize (u - w)
  have hx : 0 < x := by linarith
  have hi : x⁻¹ ≤ 2 * y⁻¹ := by
    calc x⁻¹ = 2 * (2 * x)⁻¹ := by field_simp
      _ ≤ 2 * y⁻¹ := by gcongr
  have := hQ (w - u) hx
  rw [Real.rpow_neg_one] at this
  simp only [singularPow, Real.rpow_neg_one]
  calc |Q (w - u)| ≤ B * x⁻¹ := this
    _ ≤ B * (2 * y⁻¹) := mul_le_mul_of_nonneg_left hi hB
    _ = _ := by ring

/-- The covariance cubed. -/
theorem abs_Q_cube_le {Q : SpaceTime → ℝ} {B : ℝ}
    (hQ : ∀ x, 0 < torusParabolicSize x → |Q x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ)))
    {x : SpaceTime} (hx : 0 < torusParabolicSize x) :
    |Q x| ^ 3 ≤ B ^ 3 * torusParabolicSize x ^ (-(3 : ℝ)) := by
  have h1 := hQ x hx
  have hsq : |Q x| ^ 3 ≤ (B * torusParabolicSize x ^ (-(1 : ℝ))) ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg _) h1 3
  have e : (B * torusParabolicSize x ^ (-(1 : ℝ))) ^ 3 =
      B ^ 3 * torusParabolicSize x ^ (-(3 : ℝ)) := by
    rw [mul_pow, ← Real.rpow_natCast (torusParabolicSize x ^ (-(1 : ℝ))) 3,
      ← Real.rpow_mul hx.le]
    norm_num
  exact hsq.trans e.le

end RegularityStructures

end
